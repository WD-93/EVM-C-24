{-# LANGUAGE LambdaCase #-}
module Const.Serialize where

--A module for serializing monomorphic constant expressions to assembly.
--They must be asm because they may contain functions and global pointers,
--which are unresolved labels until the asm is assembled into bytecode.

import AST.DTs
import AST.Util (rollTyApps)
import Mono.Mono (MonoS(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.List (elemIndex)
import Control.Monad (forM,forM_)
import Control.Arrow ((***))

--Serialized values are more restricted than assembly, consisting only of
--Bytes [Int] and UseLabel n (LNamed str). I therefore use a Serialized
--datatype to represent them instead of Asm.
--Why Integer length and not Int? Because otherwise
--null() :: UInt <very large number> will report an incorrect, potentially even
--negative, length.
data Serialized = Serialized {serLength :: Integer, --length in bytes
                              serSizeof :: Integer, --max length of type
                              serContent :: Content
                             }
  deriving (Eq,Ord,Read,Show)
emptySer = Serialized 0 0 []
--Invariant: Content is in normal form, i.e. there are no adjacent [Int]
--regions, no empty [Int] regions nor zero-size labels.
type Content = [Either [Int] (Int,String)]
--Quick-and-dirty solution: apply separate normalization function rather than
--merging it with concatenation and other ops.
normalizeContent :: Content -> Content
normalizeContent = go
  where go = \case
          [] -> []
          Left []:c -> go c
          Right (0,_):c -> go c
          --O(n) because I'm repeatedly left-concatenating rather than
          --right-concatenating
          Left xs : c ->
            case go c of
              Left ys : c' -> Left (xs ++ ys) : c'
              c' -> Left xs : c'
          el : c -> el : go c

--Serialization should cache datatype tags and may fail due to non-constant
--exprs.
--I don't need to worry about .data padding since I'm only generating exes
--(standalone contracts rather than dynamically includable libraries).
--By restricting myself to fully static codegen I don't need to worry about
--efficient on-chain linking.
--That means addition of constants to labels is viable, enabling
--code x = &(y.bar); code y = ...
--(x.foo) and x!ix are also viable; x = y.bar, y = ... can be optimized to
--have x point into bar. However, that requires label placement.
--Conclusion: generate a single blob that includes placelabels?
--Problem: I want to be able to inline and optimize away code globals...
--so generate a map Name => Serialized and create a compressed blob after
--pruning.
--Label values form a cyclical dependency with optimal code, but for now I'll
--just treat labels as unknown (with the possible exception of global pointers).
--Note if code xs = ImplNil@[Code,Word] (serialized length: 1),
--code y = (xs,0), the xs use must be expanded to the max size of ImplList's
--type (1+32+2 bytes).

--Label format for globals and monomorphized functions TyApp nm ts: nm++show ts.
--Using the same format for both avoids the need to use the global or defun
--set.

--Inputs:
--Module (initializers, DTsInfo, tysigs for funs and globals),
--MonoS (monomorphic datatype tags).
--Output: g => Serialized, tag scheme Map (Name,[T]) (TagScheme (E,Serialized))
--If deref is allowed then lobal initializers and tags may depend on each other,
--consider: code x = y; code y = ...
--I won't allow it for now.
--or code x = Con; data Con = Con; tag Con : T where {Con: x}
--Note for later stages: if tag or g->init are live, all fs and gs they mention
--are also live.

data SerError = MalformedConstExpr E
              --This lets me safely use Int ops in integer serialization
              | SerializedLengthExceedsCodeSizeLimit E Serialized
  deriving (Eq,Ord,Read,Show)
data SerR = SerR {
  serrTagValues :: Map (Name,[T]) (TagScheme E),
  serrSizeof :: Map (Name,[T]) Integer,
  serrDTSI :: DTsInfo E --used to map con => datatype
      }
data SerS = SerS {
  sersAllocPtr :: Int, --for static allocation of Code BDTs
  --Why include E, T? Because allocValue v :: Ptr Code a in a const leads to a
  --new code global being created, and all of its global info must be
  --available in later stages.
  --Note also that substituting allocValue for $anonCodeGlobal<n> changes the
  --E, so a new one needs to be returned in serializeE.
  sersCodeInits :: Map Name (T,E,Serialized), --mandatory for all code globals
  sersMemInits :: Map Name (T,E,Serialized),
    --optional for memory globals
  --We include the canonical con list to enable tag calc from con without
  --re-consulting DTSI.
  sersTagSchemes :: Map (Name,[T]) ([Name], TagScheme (E,Serialized)),
  --The list of allocValue vs that must be bound to the given global;
  --their serialization is performed asynchronously to avoid an infinite loop
  --in e.g. data Foo = Foo; tag Foo = Ptr Code Foo where {Foo: allocValue Foo}
  sersRunQueue :: [(Name,T,E)] --global name, type, value
  }
  deriving (Eq,Ord,Read,Show)
  
type SerM = ReaderT SerR (StateT SerS (Except SerError))

--For each mentioned global:
-- compute init if present, redundantly apply initializer rules
-- (code must init, memory may, sto+tsto may not, rest forbidden)
--For each mentioned DT:
-- If tag scheme is custom, add serialization
--Every allocValue@[Code,a] v must create a Code global.
--With no mutual dependencies I don't need to check for loops; phew!
--serializeE now updates the E (replacing allocValue c with a new code global
--pointer). That means custom tag schemes need to be updated.
--That risks introducing a cycle:
--data Foo = Foo;
--tag Foo = Ptr Code Foo where {Foo: allocValue Foo}
--How to deal with that? Sequentially serializing the v in allocValue v
--causes the loop, but thankfully we don't need to do that; instead we can
--just allocate the new code global's name, then register it for async
--serialization.
--Each allocValue is independent, there's no sharing. However, tag scheme
--serialization must be memoized to prevent repeated allocation.
--Global => tag is not a problem, only tag => tag is. Inline cycles shouldn't
--exist since Sizeof should've caught that.
serialize :: Module -> --layout info
             MonoS ->     --global and monoDT sets
             Map (Name,[T]) Integer -> --sizeof info
             Either SerError SerS
serialize m monoS monoT2sz =
  let dtsi = dtsInfo m in
    runExcept $ flip execStateT (SerS {sersAllocPtr = 1,
                                       sersCodeInits = M.empty,
                                       sersMemInits = M.empty,
                                       sersTagSchemes = M.empty,
                                       sersRunQueue = []
                                      }) $
    flip runReaderT (SerR {serrTagValues = exploredDTs monoS,
                           serrSizeof = monoT2sz,
                           serrDTSI = dtsi
                          }) $ do
    --For each global that has an initializer, run serGlobal
    let gset = S.toList $ exploredGlobals monoS
    --Because they're already monomorphic after HM, their initializers are to
    --be found in Module
    forM_ gset (\g -> do
                 let Just (r,me) = M.lookup g (globals m)
                     isCode = r == Co
                 case me of
                   Nothing -> return ()
                   Just e ->
                     let Just ([],t) = M.lookup g (tysigs m)
                     in serGlobal isCode g t e)
    --For each mentioned datatype, serialize its tags
    let dts = M.keys $ exploredDTs monoS
    forM_ dts (uncurry serDatatype)
    --Ensure the scheduled serialization tasks are run
    serScheduler

--Serializes the initializer of a code or memory global, storing the
--serialization and updated expr in the appropriate map.
--Serializing newly allocated code globals is the only task which can be
--spawned and run asynchronously.
--If isCode is True it's a code global, otherwise it's a memory global.
serGlobal :: Bool -> Name -> T -> E -> SerM ()
serGlobal isCode nm t e = do
  (e',ser) <- serializeE e
  s <- get
  if isCode
    then put s{sersCodeInits = M.insert nm (t,e',ser) $
                sersCodeInits s}
    else put s{sersMemInits = M.insert nm (t,e',ser) $
                sersMemInits s}
--Fills in the info for the monomorphic type tycon params.
--Memoizing because it may be called repeatedly.
--Returns (cons,tagScheme), all the info you need to compute a con's tag
--serialization.
serDatatype :: Name -> [T] -> SerM ([Name],TagScheme (E,Serialized))
serDatatype tycon ts = do
  m <- gets sersTagSchemes
  case M.lookup (tycon,ts) m of
    Just x -> return x
    Nothing -> do
      --Get the constructors from DTSI:
      dtsi <- asks serrDTSI
      let Just di = M.lookup tycon $ datatypes dtsi
          cons = dtCanonicalCons di
      --Serialize the monomorphic tag scheme
      --If the datatype is boxed it has the UBDT's tag scheme but no tag...
      --recurse on ImplTyCon to copy over the updated tag scheme.
      ts' <- if dtBoxed di
             then do
        (_ubcons,tagScheme') <- serDatatype ("Impl"++tycon) ts
        return tagScheme'
             else do
        tvs <- asks serrTagValues
        case M.lookup (tycon,ts) tvs of
          Nothing ->
            error $ "Compiler error: missing monomorphic tag scheme for "
            ++ tycon ++ " " ++ show ts
          Just tagScheme ->
            serTagScheme tagScheme
      let pair = (cons,ts')
      modify (\s->s{sersTagSchemes = M.insert (tycon,ts) pair $
                   sersTagSchemes s})
      return pair
serTagScheme :: TagScheme E -> SerM (TagScheme (E,Serialized))
serTagScheme tagScheme =
  case tagScheme of
    Nil -> return Nil
    N1 len -> return $ N1 len
    N16 -> return N16
    Custom t con2e ->
      Custom t <$> mapM serializeE con2e
      
{-
Valid const expr form:
Disallow *_, indexPtr, .field, arr!ix for now.
c ::= f, g, k, -k, Array es, Con {field: c}, allocValue@[Code,a] v
Q: Should I also support null()? Not for now.
Note Pair is treated specially (zero bytes are inserted).
Note zero bytes are distinct from arbitrary-valued padding!
Desirable property: I don't need to manipulate serialized values, just concat
them.
-}
serializeE :: E -> SerM (E,Serialized)
serializeE = go
  where go e =
          case e of
            --f, g
            TyApp nm ts ->
              ret (e,Serialized {serLength = 2,
                                 serSizeof = 2,
                                 serContent = [Right (2, mkLabel nm ts)]
                                })
            --k
            --Now where did I put the Integer => bytes function...?
            TyApp "fromWord" [s,TyNat len] :$ EInteger k ->
              ret (e,Serialized {serLength = len,
                                 serSizeof = len,
                                 serContent = normalizeContent
                                              [Left $ serInt len k]
                                })
            --(-k)
            TyApp "negate" _ :$
              (TyApp "fromWord" [s,TyNat len] :$ EInteger k) ->
              --Fateful choice: statically apply the negation. That breaks
              --the invariant that all integer literals are non-negative, but
              --I don't use that currently.
              ret (TyApp "fromWord" [s,TyNat len] :$ EInteger (-k)
                  , Serialized {serLength = len,
                                  serSizeof = len,
                                  serContent = normalizeContent
                                   [Left $ serInt len (-k)]
                                 })
            --Static value allocation
            --More general than just BDTs
            --Serialization of the referenced expr c must be done asynchronously
            --to prevent infinite loops.
            --Trap: the region is the second tyvar argument, unlike alloc where
            --it's the first.
            TyApp "allocValue" [a, TyCon "Code"] :$ c ->
              spawnSerializeNewGlobal a c
            --Array => just concat all values
            EArray (Just t) es -> do
              esers <- mapM go es
              --Note using foldl would be quadratic
              ret (EArray (Just t) $ map fst esers,
                   foldr concatSer emptySer $ map snd esers)
            --Note missing fields of type TyCon params become sz zero bytes,
            --where sz is sizeof (TyCon params). That means Mono must consider
            --every con argument datatype mentioned!
            --Fields may also appear out of order in ConRecords; they must be
            --placed in canonical order when serializing.
            --Pair is a special case: both fst and snd are word-padded
            ConRecord "Pair" (Just [a,b]) field_es -> do
              field_e_sers <- serializeFields [("fst",a),("snd",b)] field_es
              ret (ConRecord "Pair" (Just [a,b]) $
                   map (id *** fst) field_e_sers
                , concatSers $ map (leftPadSer . snd . snd) field_e_sers)
            --Con {field: c}
            -- Get tag (possibly empty) and fields, concat args in field order
            -- and prepend tag.
            -- Set serSizeof to max size of type
            -- Because serializeE modifies the tag, you also need to update it!
            ConRecord con (Just params) field_es -> do
              (dtSz,serTag,field_ts) <- serGetConInfo con params
              field_e_sers <- serializeFields field_ts field_es
              ret (ConRecord con (Just params) $
                  map (id *** fst) field_e_sers,
                   (concatSers $ serTag :
                    map (snd . snd) field_e_sers){serSizeof=dtSz})
              {-
              tycon <- serGetConParent con
              dtSz <- serGetSizeof (tycon,params)
              serTag <- serGetTag tycon params con
              ss <- mapM (go . snd) field_es
              --TODO fail w/ compiler error if serLength unexpectedly > sizeof
              return (concatSers (serTag:ss)){serSizeof = dtSz}
-}
            e -> throwError $ MalformedConstExpr e
        ret :: (E, Serialized) -> SerM (E,Serialized)
        ret (e,s) = if serLength s > 24000
                    then throwError $ SerializedLengthExceedsCodeSizeLimit e s
                    else return (e,s)

--Given the structure of a constructor's arguments and the given fields,
--returns their serialization in layout order with missing
--fields filled in with null().
--Precondition: no duplicate fields in either argument, field_es contains
--no fields not in field_ts, field_es is well-typed.
--Why not return a single Serialized? Because for Pair, the fst and snd fields
--must be word-padded before concatenation.
serializeFields :: [(Name,T)] -> [(Name,E)] ->
  SerM [(Name,(E,Serialized))]
serializeFields field_ts field_es = do
  let field2e = M.fromList field_es
  forM field_ts (\(field,t) ->
                   case M.lookup field field2e of
                     Nothing -> do
                       --Empty fields are null
                       sz <- serGetSizeofT t
                       return (field,(TyApp "null" [t] :$
                                      ConRecord "Unit" (Just []) [],
                                       Serialized {
                                         serSizeof = sz,
                                         serLength = sz,
                                         serContent = normalizeContent [
                                             Left $
                                             replicate (fromIntegral sz) 0]
                                         })
                              )
                     Just e -> do
                       (e',ser) <- serializeE e
                       return (field,(e',ser)))

--Spawns an asynchronous serialization task of allocValue@[Code,a] v, returning
--a reference to it. The v is allocated to a new global $anonCodeGlobal<n>.
spawnSerializeNewGlobal :: T -> E -> SerM (E,Serialized)
spawnSerializeNewGlobal t e = do
  s <- get
  let n = sersAllocPtr s
      name = "$anonCodeGlobal" ++ show n
  --Add (name,t,e) to runqueue, bump n
  put s{sersAllocPtr = n + 1,
        sersRunQueue = (name,t,e) : sersRunQueue s
       }
  return (TyApp name [],
           Serialized {serLength = 2,
                       serSizeof = 2,
                       serContent = [Right (2,mkLabel name [])]
                      })
--Runs all scheduled tasks (and their subtasks) to completion. This must be
--called for spawn to have any effect.
serScheduler :: SerM ()
serScheduler = do
  s <- get
  case sersRunQueue s of
    [] -> return ()
    (name,t,e):rest -> do
      put s{sersRunQueue = rest}
      serGlobal True {-is global-} name t e
      serScheduler
      
--Get the ConInfo of the given constructor
serGetCI :: Name -> SerM ConInfo
serGetCI con = do
  dtsi <- serrDTSI <$> ask
  case M.lookup con $ conInfo dtsi of
    Nothing -> error $ "Compiler error: missing con info for " ++ con ++
      "in serialization phase"
    Just ci -> return ci
--Get the information needed for constructor serialization:
--the size of the datatype, the serialized tag (empty if Nil or boxed), fields.
--Tag computation is memoized to prevent repeated allocation of allocValues in
--tags.
--TODO deduplicate with later logic...
--I could cache all the info rather than just the tag, but that would pollute
--the env and require I filter it later. I'll just recalculate it for now.
--TODO find a less confusing name; this doesn't return the ConInfo DT, but
--serGetCI does.
serGetConInfo :: Name -> [T] -> SerM (Integer,Serialized,[(Name,T)])
serGetConInfo con ts = do
  ci <- serGetCI con
  let tycon = conParent ci
      fields = conFields ci
  --If the DT is boxed the tag will be nil
  dtsi <- asks serrDTSI
  let Just dti = M.lookup tycon (datatypes dtsi)
      boxed = dtBoxed dti
  sz <- serGetSizeof (tycon,ts)
  --The memoized part:
  (cons,tagScheme) <- serDatatype tycon ts
  let serTag = serComputeTag boxed cons tagScheme con
  return (sz,serTag,fields)

--For tag schemes N1 n and N16, you also need the canonical con list to
--compute a constructor's tag (because it depends on the index).
--I don't return an E because there might not be one (as boxed datatypes and
--those with tag scheme Nil lack a tag).
serComputeTag :: Bool -> [Name] -> TagScheme (E,Serialized) -> Name ->
  Serialized
serComputeTag boxed cons tagScheme con
  | boxed || (tagScheme == Nil) = emptySer
  | let = case tagScheme of
            Custom t con2e_ser ->
              let Just (_e,ser) = M.lookup con con2e_ser
              in ser
            other ->
              let Just ix = elemIndex con cons
                  len = case other of
                          N1 len -> fromIntegral len
                          N16 -> 1
              in Serialized {
                serSizeof = len,
                serLength = len,
                --Note N1 never has len 0, so no need to normalizeContent
                serContent = [Left $ serInt len $
                              fromIntegral ix]
                }
{-  
  --Get the monomorphic tagScheme we prepared earlier
  monot2ts <- asks serrTagValues
  case M.lookup (tycon,ts) monot2ts of
    Nothing -> error $
      "Compiler error: Mono.Mono didn't produce a tag scheme for " ++
      show (tycon,ts)
    Just tagScheme ->
      case tagScheme of
        --Ezpz
        Nil -> return (EArray (Just $ TyCon "Whatever!") [])
          --Any 0-size expr would do
        Custom _t con2tag ->
          case M.lookup con con2tag of
            Nothing -> error $ "Compiler error: " ++ con ++ " not in " ++
                       tycon ++ "'s custom tag scheme!?"
            Just tagE -> return tagE
        other -> do
          --Now we need the con's index in tycon's canonical cons
          dtsi <- asks serrDTSI
          let Just dti = M.lookup tycon $ datatypes dtsi
              cons = dtCanonicalCons dti
              Just ix = elemIndex con cons
              litOfLen len k =
                TyApp "fromWord" [TyCon "Unsigned", TyNat $ fromIntegral len]
                :$ EInteger (fromIntegral k)
          return $ case other of
                     --Note ix <- 0..15 here
                     N16 -> litOfLen 1 (ix*16)
                     N1 len -> litOfLen len ix
-}
--Get the size of a monomorphic T :: Type
--(guaranteed to be of form TyCon params)
serGetSizeofT :: T -> SerM Integer
serGetSizeofT t =
  let (TyCon tycon, params) = rollTyApps t
  in serGetSizeof (tycon,params)
--Get the size of a monotype
serGetSizeof :: (Name,[T]) -> SerM Integer
serGetSizeof conTs = do
  sizes <- asks serrSizeof
  case M.lookup conTs sizes of
    Nothing -> error $ "Compiler error: missing sizeof for " ++ show conTs
    Just sz -> return sz
--Convert an Integer to an n-byte big-endian two's complement bytestring.
--Silently truncates if the number doesn't fit; TODO warn on precision loss.
--TODO deduplicate with existing Asm.integer2Bytes, though this one is more
--general (it handles > 32B).
--Note the programmer may select a ludicrous len
serInt :: Integer -> Integer -> [Int]
serInt len k = paddedBs
  where modulus = 256 ^ len
        --Normalize k to k'' in the range 0..modulus-1
        k' = k `mod` modulus
        k'' = if k' < 0 then k' + modulus else k'
        n2rbs 0 = []
        n2rbs n = fromInteger (n `mod` 256) : n2rbs (n `div` 256)
        bs = reverse $ n2rbs k''
        paddedBs = replicate (fromInteger len - length bs) 0 ++ bs
--When two serialized values are concatenated unboxed (either in an Array or
--unboxed constructor), each value is extended to its sizeof by zero-padding
--it to the right.
concatSer :: Serialized -> Serialized -> Serialized
concatSer s1 s2 =
  let s1' = rightPadSer s1
      s2' = rightPadSer s2
      len = serSizeof s1' + serSizeof s2'
  in Serialized {serLength = len,
                 serSizeof = len,
                 serContent = normalizeContent $ serContent s1 ++ serContent s2
                }
concatSers :: [Serialized] -> Serialized
concatSers = foldr concatSer emptySer

--If the serialized value is smaller than its type's maximum size
--(e.g. unboxed Nil or Nothing), pad to the right with zero bytes.
rightPadSer :: Serialized -> Serialized
rightPadSer s
  | serLength s > serSizeof s =
    error $ "Compiler error: serLength > serSizeof in " ++ show s
  | serLength s == serSizeof s = s
  | let diff = serSizeof s - serLength s =
          s{serLength = serSizeof s,
            serContent = normalizeContent $
                         serContent s ++ [Left $ replicate (fromInteger diff) 0]
           }
--Left-pad the value to a whole number of words; first extend it to max size.
--Ex: Nil :: List Memory Bool => 28B left-padding, 0x00, 3B right-padding.
leftPadSer :: Serialized -> Serialized
leftPadSer s =
  let s' = rightPadSer s
      sz = serSizeof s'
      paddedSz = sz `roundedUpMod` 32
      padRequired = paddedSz - sz
  in s'{serSizeof = paddedSz,
        serLength = paddedSz,
        serContent = normalizeContent $
                     Left (replicate (fromInteger padRequired) 0) :
                     serContent s'
       }
--The label format for functions and globals
mkLabel :: Name -> [T] -> String
mkLabel nm ts = nm ++ show ts
