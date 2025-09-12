{-# LANGUAGE LambdaCase #-}
module Const.Serialize where

--A module for serializing monomorphic constant expressions to assembly.
--They must be asm because they may contain functions and global pointers,
--which are unresolved labels until the asm is assembled into bytecode.

import AST.DTs
import Mono.Mono (MonoS(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.List (elemIndex)

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
  --Why include the E? Because new code globals may be allocated and we might
  --want to apply opts which depend on symbolically evaluating them.
  --Why do the same for mem? Because a map of tuples is cheaper than a tuple
  --of maps.
  sersCodeInits :: Map Name (E,Serialized), --mandatory for all code globals
  sersMemInits :: Map Name (E,Serialized),  --optional for memory globals
  sersTagSchemes :: Map (Name,[T]) (TagScheme (E,Serialized))
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
serialize :: DTsInfo E -> --layout info
             MonoS ->     --global and monoDT sets
             Map (Name,[T]) Integer -> --sizeof info
             Either SerError SerS
serialize dtsi monoS monoT2sz = error "todo"

{-
Valid const expr form:
Disallow *_, indexPtr, .field, !ix for now.
c ::= f, g, k, -k, Array es, Con {field: c}, allocValue@[Code,a] v
Q: Should I also support null()? Not for now.
Note Pair is treated specially (zero bytes are inserted).
Note zero bytes are distinct from arbitrary-valued padding!
Desirable property: I don't need to manipulate serialized values, just concat
them.
-}
serializeE :: E -> SerM Serialized
serializeE = go
  where go e =
          case e of
            --f, g
            TyApp nm ts ->
              ret e $ Serialized {serLength = 2,
                                  serSizeof = 2,
                                  serContent = [Right (2, mkLabel nm ts)]
                                 }
            --k
            --Now where did I put the Integer => bytes function...?
            TyApp "fromWord" [s,TyNat len] :$ EInteger k ->
              ret e $ Serialized {serLength = len,
                                  serSizeof = len,
                                  serContent = normalizeContent
                                               [Left $ serInt len k]
                                 }
            --(-k)
            TyApp "negate" _ :$
              (TyApp "fromWord" [s,TyNat len] :$ EInteger k) ->
              ret e $ Serialized {serLength = len,
                                  serSizeof = len,
                                  serContent = normalizeContent
                                   [Left $ serInt len (-k)]
                                 }
            --Array => just concat all values
            EArray (Just _t) es -> do
              ss <- mapM go es
              --Note using foldl would be quadratic
              ret e $ foldr concatSer emptySer ss
            --Pair is a special case: both fst and snd are word-padded
            --Con {field: c}
            -- Get tag (possibly empty), concat args and prepend tag
            -- Set serSizeof to max size of type 
            ConRecord con (Just params) field_es -> do
              tycon <- serGetConParent con
              dtSz <- serGetSizeof (tycon,params)
              serTag <- serGetTag tycon params con >>= go
              ss <- mapM (go . snd) field_es
              --TODO fail w/ compiler error if serLength unexpectedly > sizeof
              return (concatSers (serTag:ss)){serSizeof = dtSz}
            e -> throwError $ MalformedConstExpr e
        ret :: E -> Serialized -> SerM Serialized
        ret e s = if serLength s > 24000
                  then throwError $ SerializedLengthExceedsCodeSizeLimit e s
                  else return s

--Get the datatype to which a constructor belongs
serGetConParent :: Name -> SerM Name
serGetConParent con = do
  dtsi <- serrDTSI <$> ask
  case M.lookup con $ conInfo dtsi of
    Nothing -> error $ "Compiler error: missing con info for " ++ con ++
      "in serialization phase"
    Just ci -> return $ conParent ci
--Get the monomorphic tag expr of a con in tycon params
--TODO deduplicate with later logic...
serGetTag :: Name -> [T] -> Name -> SerM E
serGetTag tycon ts con = do
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
