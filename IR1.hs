{-# LANGUAGE LambdaCase, GADTs, OverloadedStrings #-}
module IR1 where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Fail
import Control.Arrow ((***))
import Data.Char (ord,isUpper) --for string compilation
--isUpper is for checking a var is a constructor

import DTs
--The logic for assembling structs from field values, split out into another
--module:
import qualified BuildStruct as B

--The first stage of compilation from AST: word-level ops with structured
--patterns.
--Function call is treated as an op.
data IRT = Mem --has no runtime repr
         | W Int T --nth word of C-level t; 1-indexed
         --Renamed from Word to avoid clash with Padding
  deriving (Eq,Ord,Read,Show)
--Name mangling: nth word of local x becomes x#n
--From ToyCFG: IR is tagged with () or Live annots.
--It does not need a var type param because SSA is done on CFG's.
data IRP a = Op a [(Name,IRT)] Operator [Name]
               | Ifte a Name [IRP a] [IRP a]
               | While a [IRP a] Name [IRP a]
               | DoWhile a [IRP a] [IRP a] Name --body, cond
               | Return a [Name]
               | Break a Int
               | Continue a Int
               | TailCall a Name [Name]
               | IRComment String --Ignored in later stages, used for debugging
               --Branching EVM instructions
               | EVM_RETURN a Name Name Name -- $mem, ptr, len
  deriving (Eq,Ord,Read,Show)
type IR = IRP ()
data Operator = Push StaticValue
              | Opcode String
              | Call --args: f, args, ret
              | Reduce Name --arg: a commutative and associative opcode,
                --used for truthy
              | Copy --x = y => x = copy [y]
  deriving (Eq,Ord,Read,Show)
--Ret and f are created by push staticValue
data StaticValue = Const Integer
                 | LabelConst Name
  deriving (Eq,Ord,Read,Show)

--Convert a defun to a sequence of IR1 ops.
--If any modification to $mem is made, it must be returned.
--If it happens in an ifte branch that returns, don't propagate (the branch
--doesn't have a successor).
--Reader: module (only function types relevant for now).
--State: C variable scope
--Only PVar and PTup assignment supported for now
--x = y becomes a renaming, but it's a pseudo-op.
--Emit: IR1 ops
type Seq = ExceptT SeqError
  (ReaderT SeqR
   (WriterT [IR]
    (State SeqS)))
runSeq :: Seq a -> SeqR -> SeqS -> (Either SeqError a,
                                     [IR],
                                     SeqS)
runSeq seq seqr s = let
  x1 = runExceptT seq
  x2 = runReaderT x1 seqr
  x3 = runWriterT x2
  x4 = runState x3 s
  in case x4 of
       ((ei,ir),s) -> (ei,ir,s)
data SeqError = UnboundVar Name
              --The stuff that can go wrong in an op
              | IlltypedLHS Name IRT IRT
              | DuplicateVarsInLHS Name (Set Name)
              | Can'tCopyUnboundIRVar Name
              | UnboundVarInOpRHS Name [(Name,IRT)] Operator [Name]

              | Couldn'tLookupVarTypeInEDSL Name
              | BadArgsInEDSL Operator [EVar]
              | BadFirstRHSInAssign Name (Maybe IRT) [Name]
              --C-level type errors
              | BadFunctionType Name T
              | Can'tAssignToFunction Name
              | Can'tAssignToPrimFun Name --it's useful to distinguish
              | ApplicationToNonFunction E T
              | BadArgInTruthy [Name]
              | BadArgPrimFun Name T
              --Errors from pattern matching
              | PTupNonTuple [Pat] T
              | PTupLengthMismatch [Pat] [T]
              --Type synonym errors
              | TySynsShadowPrimTySyns (Set Name)
              --Innovation: a single constructor for locating errors,
              --structuring the error type into context-specific types
              | InTySyn Name InTySynErr
              --The error below isn't really specific to one syn...
              | FoundTySynCycle [Name]
              | UnderAppliedSynInDefun Name [T]
              --Substituting
              | ArgsAppliedToStructInDefun [Field T] [T]
              --A placeholder error to avoid having to add new error types
              --constantly while developing
              | GenericError String
  deriving (Eq,Ord,Read,Show)
data InTySynErr = TyConOOS Name | TyVarOOS Name | TySynRepeatedArgs [Name]
  | UnderAppliedSyn Name | ArgsAppliedToStruct [Field T]
  deriving (Eq,Ord,Read,Show)
--pronounced seek s...
data SeqS = SS {
  --IR vars = v#1..n for each v in C locals, plus anonymous vars and $mem
  irLocalTypes :: Map Name IRT,
  cLocalTypes :: Map Name T,
  anonVarCounter :: Int, --makes $anonN
  --Static data support
  anonLabelCounter :: Int,
  --prepended to each time a new anon staticData is allocated
  anonStaticData :: [Static]
  }
  deriving (Eq,Ord,Read,Show)
--So I can add info about the function being compiled, specifically the return
--type but maybe more stuff in future (opt choices?).
data SeqR = SR {
  seqrModule :: Module,
  seqrFunction :: D
  --name => (region = memory | storage | tstorage, t, offset)
  --seqrGlobals :: Map Name (T,T,Int)
  --I'll substitute globals, arrays and constants in a separate pass,
  --so seqr doesn't need them.
               }
  deriving (Eq,Ord,Read,Show)
--Top-level function: given a module, generates the IR for each function.
--Pruning based on actual calls made from main can be done later.
--FW problem: the IR output may need additional info for placement, such as
--whether the code is a library, exported functions and JTs
data IRModule = IRM {
  irDefuns :: Map Name (Arity,[IR]),
  --Static data: strings, arrays, nested modules
  --For now, just strings
  --(Name,Int) is a label use, Int a byte
  --C-allocated anon label format: fname.static#n
  --That ensures the counter needn't be shared between function compilations
  staticData :: Map Name Static
  }
  deriving (Eq,Ord,Read,Show)
--Not very storage-efficient for strings...
type Static = (T,[Either (Name,Int) Int])
--The number of argument words a function takes beyond $ret; needed for asm
--generation.
type Arity = Int
--Change now that I have strings: instead of a mapM, thread through the
--anonLabelCounter and accumulate the staticData.
seqModule :: Module -> Either SeqError IRModule
seqModule mod = do
  --First, handle tysyns. After this phase they're irrelevant to output,
  --having been substituted away. However, they should still be in the
  --interface info.
  mod' <- handleTySyns mod
  let mod = mod'
  let fdefs = M.toList $ defuns mod
  checkDatatypesValidity $ datatypes mod
  globalMap <- handleGlobals $ globals mod
  --We substitute the globals and the special constant names
  --memOffset, stoOffset and tstoOffset prior to Seq to simplify seqE
  --TODO add tag_Con_TyCon constants as well; only one is needed even for
  --parameterized datatypes.
  fdefs' <- substGlobalsInDefs globalMap fdefs
  let fdefs = fdefs'
  (sd,irdefs) <- handleDefuns mod fdefs
  return $ IRM {irDefuns = M.fromList irdefs,
                staticData = sd
               }
    where handleDefuns :: Module -> [(Name,D)] ->
                          Either SeqError
                          (Map Name Static, [(Name,(Arity,[IR]))])
          handleDefuns mod = go mod 1 M.empty
          --anon label counter, static data, remaining defuns
          go :: Module -> Int -> Map Name Static -> [(Name,D)] ->
            Either SeqError (Map Name Static, [(Name,(Arity,[IR]))])
          go mod alc sd = \case
            [] -> return (sd,[])
            (fnm,defun):rest ->
              --Caught bug: tysyn substitution in constructors was being lost
              --because let mod = mod' isn't visible here
              let seqr = SR {seqrModule = mod,
                             seqrFunction = defun
                            }
                  seqs = SS {irLocalTypes = M.empty,
                             cLocalTypes = M.empty,
                             anonVarCounter = 0,
                             anonLabelCounter = alc,
                             anonStaticData = []
                            }
              in case runSeq (seqDefun defun) seqr seqs of
                   (Left serr, _, _) -> Left serr
                   (Right arity, irs, seqs') -> do
                     let alc' = anonLabelCounter seqs'
                     (sd',res) <- go mod alc'
                                  (M.union sd $ M.fromList $ zip
                                   (map (\n -> fnm ++ ".static#" ++ show n)
                                    [alc..alc'])
                                   (reverse $ anonStaticData seqs'))
                                  rest
                     return $ (sd',(fnm,(arity,irs)) : res)

--Checks the following conditions:
--1) Each datatype must have at least one param: the region.
--2) Datatypes may not have duplicate params.
--3) Datatypes may not contain duplicate constructor names.
--4) A constructor's argument must be determined by the datatype params.
--5) Given the constructor's argument is monomorphic, only the first param
--(i.e. the region param) may be free.
checkDatatypesValidity :: Map Name ([Name],[(Name,T)]) ->
                          Either SeqError ()
checkDatatypesValidity nm2dt = do
  let nmdts = M.toList nm2dt
  mapM_ (\(tycon,(params,constructors)) -> do
            vars <- checkParams tycon params
            --This won't fail because we now know params is nonempty
            let r = head params
            go tycon vars r S.empty constructors) nmdts
    where checkParams = gop S.empty
          gop s tycon []
            | s == S.empty =
              Left $ GenericError $
              "Datatype " ++ tycon ++ " has no params, but " ++
              "it must have at least one: the region"
            | let = return s
          gop s tycon (param:params)
            | S.member param s =
              Left $ GenericError $
              "Duplicate type parameter in datatype " ++ tycon ++ ": " ++ param
            | let = gop (S.insert param s) tycon params
          go :: Name -> Set Name -> Name -> Set Name -> [(Name,T)] ->
                Either SeqError ()
          go tycon params r cons = \case
            [] -> return () --0-constructor datatypes are OK
            (con,t):rest
              | S.member con cons ->
                Left $ GenericError $
                "Duplicate constructor in datatype " ++ tycon ++ ": " ++ con
              | let ->
                let free = freeTyVars t
                in case () of
                     --4) Params must fix argument
                     _ | params `S.isProperSubsetOf` free ->
                         Left $ GenericError $
                         "Free tyvars in constructor " ++ con ++ " of datatype "
                         ++ tycon ++ ": " ++ show (S.difference free params)
                       --5) Argument + region must fix params
                       | (S.insert r free) `S.isProperSubsetOf` params ->
                         Left $ GenericError $
                         "Argument + region don't fix params in constructor "++
                         con ++ " of datatype " ++ tycon
                       | let ->  go tycon params r (S.insert con cons) rest

--TODO replace with generic implementation, move somewhere appropriate.
freeTyVars :: T -> Set Name
freeTyVars = go
  where go = \case
          TyVar nm -> S.singleton nm
          tf :$$ tx -> S.union (go tf) (go tx)
          Struct padnmts -> S.unions $ map (\(_,_,t) -> go t) padnmts
          _ -> S.empty
--Takes a list of (global name, region, type, maybe arrlen) and returns
--memory, storage and storage offsets + a single map name => (r,t,off)
--Oh no: I need to be in Seq to get numBytesT
--While datatypes are always 16 bits, newtypes are not... but I just need to
--pass a newtype map to get the necessary info for size.
handleGlobals :: [(Name,T,T,Maybe Int)] -> Either SeqError
  (Int,Int,Int, Map Name (T,T,Int,Maybe Int))
handleGlobals = go M.empty $ M.fromList [(Memory,0),
                                         (Storage,0),
                                         (TStorage,0)]
  where
    go :: Map Name (T,T,Int,Maybe Int) -> Map T Int ->
          [(Name,T,T,Maybe Int)] ->
          Either SeqError
          (Int,Int,Int, Map Name (T,T,Int,Maybe Int))
    go gs offs = \case
          [] -> let moff = offs M.! Memory
                    soff = offs M.! Storage
                    tsoff = offs M.! TStorage
                in if (maximum [moff,soff,tsoff] > 65535)
                   then Left $ GenericError $
                        "Maximum representable offset exceeded in globals: "
                        ++ show (moff,soff,tsoff)
                   else return (moff,soff,tsoff,gs)
          (nm,r,t,mlen):rest ->
            let len = case mlen of
                        Just len -> len
                        Nothing -> 1
            in case M.lookup nm gs of
                 Nothing ->
                   let sz = (pureSz t `roundedUpMod` 8) `div` 8
                   in case M.lookup r offs of
                        Just off ->
                          go (M.insert nm (r,t,off,mlen) gs)
                          (M.insert r (off+len*sz) offs) rest
                        Nothing -> error $ "Compiler error: bad region " ++
                          show r ++ " in global " ++ nm
                 Just _ -> error $ "Compiler error: duplicate global " ++ nm ++
                           " not caught in desugaring phase"
--TODO replace with Generic implementation
substGlobalsInDefs :: (Int,Int,Int, Map Name (T,T,Int,Maybe Int)) ->
                [(Name,D)] -> Either SeqError [(Name,D)]
substGlobalsInDefs gm = mapM (substGlobalsInDef gm)
substGlobalsInDef gm (nm,Defun _ t pat block) = do
  pat' <- substGlobalsInPat gm pat
  block' <- mapM (substGlobalsInS gm) block
  return (nm,Defun nm t pat' block')
substGlobalsInPat gm@(moff,soff,tsoff,vm) =
  let r = substGlobalsInPat gm
      re = substGlobalsInE gm
  in \case
    PVar nm
      | nm `elem` words "memOffset stoOffset tstoOffset" ->
        Left $ GenericError $ "Special constant name " ++ nm ++
        " used as pattern variable"
      | Just (r,t,off,mlen) <- M.lookup nm vm ->
          case mlen of
            Just len -> Left $ GenericError $ "Array used as pat var: " ++
                        show nm
            Nothing -> return $ Deref (Coerce (Ptr r t) $ EInteger $
                                      fromIntegral off)
    PStruct mnmps ->
      let (mnms,ps) = unzip mnmps
      in PStruct <$> zip mnms <$> mapM r ps
    PTup ps -> PTup <$> mapM r ps
    PDot p nm -> flip PDot nm <$> r p
    PHash p ix -> flip PHash ix <$> r p
    Deref e -> Deref <$> re e
    p -> return p
substGlobalsInS gm =
  let r = substGlobalsInS gm
      re = substGlobalsInE gm
  in \case
    p := e -> (:=) <$> substGlobalsInPat gm p <*> re e
    DTs.Return e -> DTs.Return <$> re e
    DTs.Ifte e th el -> DTs.Ifte <$> re e <*> mapM r th <*> mapM r el
    DTs.While e bl -> DTs.While <$> re e <*> mapM r bl
substGlobalsInE :: (Int,Int,Int, Map Name (T,T,Int,Maybe Int)) -> E ->
                   Either SeqError E
substGlobalsInE gm@(moff,soff,tsoff,vm) =
  let r = substGlobalsInE gm
  in \case
    Var "memOffset" -> return $ EInteger $ fromIntegral moff
    Var "stoOffset" -> return $ EInteger $ fromIntegral soff
    Var "tstoOffset" -> return $ EInteger $ fromIntegral tsoff
    Var nm
      | Just (r,t,off,mlen) <- M.lookup nm vm ->
        return $
        (if mlen == Nothing then (Var "deref" :$) else id) $
        Coerce (Ptr r t) $ EInteger $ fromIntegral off
    f :$ x -> (:$) <$> r f <*> r x
    EStruct padmnmes ->
      let padmnms = map (\(pad,mnm,_) -> (pad,mnm)) padmnmes
          es = map (\(_,_,e) -> e) padmnmes
      in EStruct <$> zipWith (\(pad,mnm) e -> (pad,mnm,e)) padmnms <$>
         mapM r es
    e :. nm -> (:. nm) <$> r e
    e :# ix -> (:# ix) <$> r e
    Coerce t e -> Coerce t <$> r e
    Con con arg alloc -> Con con <$> r arg <*> substGlobalsInPat gm alloc
    e -> return e
                           
--TODO give newtypes param, then reimplement numBitsT in terms of pureSz
pureSz :: T -> Int
pureSz = \case
  Int _ n -> fromInteger n
  a :-> b -> 16
  Ptr r a -> 16
  Struct padnmts ->
    let padalszs = map (\((pad,al),_,t) ->
                            let sz = pureSz t
                            in (pad,al,sz)) padnmts
        (sz,structure) = B.structLayout padalszs
    in sz
  --Datatypes are just wrapped pointers
  TyCon _ -> 16
  _ :$$ _ -> 16
  t -> error $ "Compiler error: undefd numBitsT for " ++ show t


--First checks for cycles in the type synonyms.
--Substitute all types and check their kinds. It's disappointing that can't
--be done in the Seq monad...
--The desugaring phase has already ruled out tysyns clashing with other defs.
--While the kind check is deferred until use rather than done in the check of
--the type decl itself, I can check whether the tysyn RHS contains type
--constructors that aren't in scope.
--For now, that only includes the primitive tycons.
--Now I also need to subst tysyns in datatypes.
handleTySyns :: Module -> Either SeqError Module
handleTySyns mod = do
  --We must first add the primitive tysyns to prevent out of scope errors for
  --them.
  let i = S.intersection (M.keysSet primTySyns) (M.keysSet $ tysyns mod)
  if i /= S.empty
    then Left $ TySynsShadowPrimTySyns i
    else return ()
  let ts = M.union primTySyns $ tysyns mod
  checkForCycles mod{tysyns = ts}
  --For each tysyn, substitute all tysyns (fails if they're not fully applied)
  --Result: type Syn args = T<args>, where T contains no tysyns
  --We also add the primitive tysyns here; TODO break them out into a module
  --a la GHC.Prim?
  tysyns' <- substTySyns ts
  --For each defun, substitute the type signature.
  defuns' <- substDefuns tysyns' mod
  --Substitute tysyns and globals in static data
  static' <- substStatic tysyns' $ static mod
  globals' <- substGlobals tysyns' $ globals mod
  datatypes' <- substDatatypes tysyns' $ datatypes mod
  constructors' <- substConstructors tysyns' $ constructors mod
  --TODO add coerce and substitute in the function body
  return mod{tysyns = tysyns',
             defuns = defuns',
             static = static',
             globals = globals',
             datatypes = datatypes',
             constructors = constructors'
             }
substConstructors :: Syns -> Map Name (Int,T,Name,Name,[Name]) ->
                     Either SeqError (Map Name (Int,T,Name,Name,[Name]))
substConstructors syns con2info = do
  let coninfos = M.toList con2info
  M.fromList <$> mapM (\(con,(tag,arg,tycon,r,params)) ->
                         case applyTySyns syns arg of
                           Left err ->
                             Left $ GenericError $
                             "Tysyn application error in constructor " ++ con
                             ++ ": " ++ show err
                           Right arg' -> return (con,(tag,arg',tycon,r,params)))
    coninfos
substDatatypes :: Syns -> Map Name ([Name],[(Name,T)]) ->
                  Either SeqError (Map Name ([Name],[(Name,T)]))
substDatatypes syns tycon2ds = do
  let tyconds = M.toList tycon2ds
      --Putting it here because otherwise it's indented too far to the right...
      innerLoop tycon (constructor,t) =
            case applyTySyns syns t of
              Left err -> Left $ GenericError $
                          "Tysyn application error in constructor " ++
                          constructor ++ " in datatype " ++ tycon ++ ": " ++
                          show err
              Right t' -> return (constructor, t')
  M.fromList <$> mapM (\(tycon,(params,cons)) -> do
                          cons' <- mapM (innerLoop tycon) cons
                          return (tycon,(params,cons'))) tyconds
substStatic syns nm2tes = do
  let nmtes = M.toList nm2tes
  M.fromList <$> mapM (\(nm,(t,es)) ->
                         case applyTySyns syns t of
                           Left err -> Left $
                             GenericError $ "Tysyn application error in " ++
                             "static data " ++ nm ++ ": " ++ show err
                           Right t' -> return (nm,(t',es))) nmtes
substGlobals syns nm_region_ts =
  mapM (\(nm,r,t,mlen) ->
          case applyTySyns syns t of
            Left err -> Left $ GenericError $ "Tysyn error in global " ++
                        nm ++ ": " ++ show err
            Right t' -> return (nm,r,t',mlen)) nm_region_ts
--What can go wrong? An underapplied syn or a kind check failure.
--In future the kind check will need to consider user-defined types.
--Without a kind check on data decl creation, you need to defer the check until
--data types are fully applied and then see whether their constructor args are
--Type (or in future, a non-stack value type).
--For now I'll just do the substitution.
--Edit: adding substitution in the function body.
substDefuns :: Syns -> Module -> Either SeqError (Map Name D)
substDefuns syns mod = do
  let defs = map snd $ M.toList $ defuns mod
  sdefs <- mapM (\case Defun fnm t pat body -> do
                         t' <- substDefunT t
                         body' <- mapM (substTySynS syns) body
                         return $ (fnm,Defun fnm t' pat body')) defs
  return $ M.fromList sdefs
  where substDefunT t =
          case applyTySyns syns t of
            Left (Left (nm,ts)) -> Left $ UnderAppliedSynInDefun nm ts
            Left (Right (pnts,ts)) -> Left $ ArgsAppliedToStructInDefun pnts ts
            Right t' -> Right t'

--TODO switch to generic implementation...
substTySynS :: Syns -> S -> Either SeqError S
substTySynS syns =
  let r = substTySynS syns
      re = substTySynE syns
      rp = substTySynPat syns
  in \case
    p := e -> (:=) <$> rp p <*> re e
    DTs.Return e -> DTs.Return <$> re e
    DTs.Ifte b th el -> DTs.Ifte <$> re b <*> mapM r th <*> mapM r el
    DTs.While e body -> DTs.While <$> re e <*> mapM r body
substTySynE :: Syns -> E -> Either SeqError E
substTySynE syns =
  let r = substTySynE syns
  in \case
    f :$ x -> (:$) <$> r f <*> r x
    EStruct fields -> EStruct <$>
      mapM (\(p,mnm,e) -> do
               e' <- r e
               return (p,mnm,e')) fields
    e :. field -> (:. field) <$> r e
    e :# ix -> (:# ix) <$> r e
    --The one interesting case
    Coerce t e ->
      case applyTySyns syns t of
        Left err -> Left $ GenericError $ "TySyn subst in coerce failed: "
          ++ show (t,e,err)
        Right t' -> Coerce t' <$> r e
    Con con arg alloc ->
      Con con <$> r arg <*> substTySynPat syns alloc
    e -> return e
substTySynPat :: Syns -> Pat -> Either SeqError Pat
substTySynPat syns =
  let r = substTySynPat syns
      re = substTySynE syns
  in \case
    PStruct mnmps -> PStruct <$> mapM (\(mnm,p) -> do
                                          p' <- r p
                                          return (mnm,p')) mnmps
    PTup ps -> PTup <$> mapM r ps
    PDot p nm -> (`PDot` nm) <$> r p
    PHash p ix -> (`PHash` ix) <$> r p
    Deref e -> Deref <$> re e
    p -> return p
{-
--Applies a map of tysyns to a type, potentially producing an underapplied
--syn error or args applied to struct. TODO deduplicate
applyTySyns :: Syns -> T -> Either (Either (Name,[T])
                                    ([Field T],[T])) T
-}
      
--Accumulate a map of fully expanded tysyns, containing no other syns
--When exploring a syn, if you encounter another syn then explore it before
--attempting to apply it. The absence of cycles will ensure this terminates.
type Syns = Map Name ([Name],T)
substTySyns :: Syns -> Either SeqError Syns
substTySyns syns =
  runExcept (execStateT (mapM_ (substTySynsM syns) $ M.keys syns) M.empty)
substTySynsM :: Syns -> Name -> StateT Syns (Except SeqError) ()
substTySynsM oldSyns syn = do
  done <- gets (M.member syn)
  if done
    then return ()
    else do
    let (args,t) = oldSyns M.! syn
    t' <- substTySynT syn t
    modify (M.insert syn (args,t'))
    where
      --The syn is just for error reporting
      --TODO deduplicate: first get the set of referenced syns (using a
      --preexisting function), use substTySynsM to initialize them, then
      --use applyTySyns with the state.
      substTySynT syn t = do
        let (tf,targs) = collectTyApps t
        targs' <- mapM (substTySynT syn) targs
        --If tf is a tysyn, it may be overapplied
        case tf of
          TyCon nm
            | M.member nm oldSyns -> do
                substTySynsM oldSyns nm
                (args,template) <- gets (M.! nm)
                let argslen = length args
                if argslen > length targs
                  then lift $ throwE $ InTySyn syn (UnderAppliedSyn nm)
                  else do
                  let targsPrefix = take argslen targs
                      targsSuffix = drop argslen targs
                      res = applyTySyn args template targsPrefix
                  return $ unCollectTyApps res targsSuffix
          Struct pnts ->
            if null targs
            then Struct <$> mapM (\(pad,mnm,t) -> do
                                     t' <- substTySynT syn t
                                     return (pad,mnm,t')) pnts
            else lift $ throwE $ InTySyn syn (ArgsAppliedToStruct pnts)
          _ -> return $ tf `unCollectTyApps` targs'
          
--Applies a map of tysyns to a type, potentially producing an underapplied
--syn error or args applied to struct. TODO deduplicate
applyTySyns :: Syns -> T -> Either (Either (Name,[T])
                                    ([Field T],[T])) T
applyTySyns syns t = do
  let (tf,targs) = collectTyApps t
      r = applyTySyns syns
  targs' <- mapM (applyTySyns syns) targs
  case tf of
    TyCon nm
      | Just (vars,template) <- M.lookup nm syns -> do
          let varslen = length vars
          if varslen > length targs'
            then Left $ Left (nm,targs') --underapplied syn
            else do
            let targsPre = take varslen targs'
                targsSuf = drop varslen targs'
            return $ applyTySyn vars template targsPre
              `unCollectTyApps` targsSuf
    Struct pnts ->
      if null targs
      then Struct <$> mapM (\(p,n,t) -> do
                               t' <- r t
                               return (p,n,t')) pnts
      else Left $ Right (pnts,targs)
    _ -> return $ tf `unCollectTyApps` targs'
--Performs a single instantiation of a tysyn.
--Precondition: the length of vars and ts match
--TODO use generic
applyTySyn vars template ts =
  go template
  where
    substMap = M.fromList $ zip vars ts
    go = \case
      --The earlier scope check guarantees this is in substMap, but it's worth
      --having a custom error just in case
      TyVar nm ->
        case M.lookup nm substMap of
          Nothing -> error $ "Compiler error: unknown var in applyTySyn: "++nm
          Just t -> t
      tf :$$ tx -> go tf :$$ go tx
      Struct pnts -> Struct $ map (\(p,n,t) -> (p,n,go t)) pnts
      t -> t
findCycle :: Ord k => Map k (Set k) -> Either [k] ()
findCycle m =
  case mapM_ (findCycleM m [] S.empty) $
         M.keys m of
    Left path -> Left path
    Right _ -> Right ()
--Simplicity before efficiency... I'll remove memoization for now
findCycleM :: Ord k => Map k (Set k) -> [k] -> Set k -> k -> Either [k] ()
findCycleM m stk s k
  | S.member k s = Left $ reverse stk
  | otherwise = do
      let stk' = k:stk
          s' = S.insert k s
          ks = S.toList $ m M.! k
      mapM_ (findCycleM m stk' s') ks

checkForCycles :: Module -> Either SeqError ()
checkForCycles mod = do
  scopeCheckSyns --todo add data decls
  case findCycle syn2syns of
    Left path -> Left $ FoundTySynCycle path
    Right () -> Right ()
  where
    --Errors: tycon out of scope, tyvar out of scope
    --Repeated arg vars are an error; we check for it here
    scopeCheckSyns = mapM_ (\(synnm,(args,t)) ->
                              if S.size (S.fromList args) /=
                                 length args
                              then Left $ InTySyn synnm (TySynRepeatedArgs args)
                              else scopeCheckSyn synnm args t)
                     $ M.toList $ tysyns mod
    --We don't check for underapplied tysyns here, just scope
    --How to mitigate type FixedPoint f = f f without kinds?
    --At application: substitute recursively;
    --an underapplied tysyn is not a valid argument.
    scopeCheckSyn synnm args =
      let r = scopeCheckSyn synnm args in
      \case
      TyCon nm ->
        case staticNameInfo nm mod of
          IsPrimTyCon -> return ()
          IsTySyn -> return ()
          IsUnbound -> Left $ InTySyn synnm (TyConOOS nm)
          ni -> error $ "Compiler error: unexpected name info for tycon"
      TyVar nm
        | nm `elem` args -> return ()
        | otherwise -> Left $ InTySyn synnm (TyVarOOS nm)
      tf :$$ tx -> r tf >> r tx
      TyNat n -> return ()
      Struct padmnmts -> sequence_ [r t | (pad,mnm,t) <- padmnmts]
    syn2syns :: Map Name (Set Name)
    syn2syns = M.map (\(args,t) -> collectSubSyns mod t)
               $ tysyns mod
--TODO use generic programming to simplify
collectSubSyns :: Module -> T -> Set Name
collectSubSyns mod =
  let r = collectSubSyns mod in
    \case
      TyCon nm
        | IsTySyn <- staticNameInfo nm mod ->
            S.singleton nm
      tf :$$ tx ->
        S.union (r tf) (r tx)
      Struct pnts ->
        S.unions $ map r $ map (\(_,_,t) -> t) pnts
      _ -> S.empty
--Might be generally useful
collectTyApps :: T -> (T,[T])
collectTyApps = \case
  tf :$$ tx ->
    let (f,args) = collectTyApps tf
    in (f,args ++ [tx])
  t -> (t,[])
unCollectTyApps :: T -> [T] -> T
unCollectTyApps tf = \case
  [] -> tf
  x:xs -> (tf :$$ x) `unCollectTyApps` xs
  
--Find info about a name defined at the module level.
--Postcond: will not be an IsLocal.
--Warning: if you call this on a module before tysyn substitution, the type in
--IsFunction will be unsubstituted!
--Primitive tysyns are described as IsTySyns
staticNameInfo :: Name -> Module -> NameInfo
staticNameInfo nm mod
  | S.member nm primTyCons = IsPrimTyCon
  | S.member nm primFunSet = IsPrimFun
  | M.member nm $ tysyns mod = IsTySyn
  | Just (Defun _ t _ _) <- M.lookup nm $ defuns mod = IsFunction t
  | otherwise = IsUnbound

askModule :: Seq Module
askModule = seqrModule <$> ask
askReturnType :: Seq T
askReturnType = do
  Defun nm t _lhs _body <- seqrFunction <$> ask
  case t of
    a :-> b -> return b
    _ -> throwE $ BadFunctionType nm t
{-
Consider
while(e)
 tmp = x
 x = y
 y = tmp

The renaming ops become noops in the next stage, but they change the stack
layout. Let's say the starting layout in loop is x,y,vs. The target layout
at the end of the loop becomes y,x,vs after translation; consequently, a swap
must be emitted.
Invariant: only one version of a C-level var word is live at a time; garbage
words may be substituted for any other garbage. Avoid leaving any garbage at
the end of a SLC?
-}
--Args: $mem : Mem, arg words, $ret : tword
--Start with args in scope at the C and IR level
--For now, support only x and (p1,p2,p3) patterns (PVar and PTup)
--The argument words are initially anonymous; bind them to variables using the
--same pattern-matching logic as assignment.
seqDefun :: D -> Seq Arity
seqDefun (Defun f ft pat body) =
  case ft of
    a :-> b -> do
      --Get arity to return
      arity <- numWordsT a
      --Match argument against lhs
      args <- anonVarsT a
      patternMatch pat a args
      --The return address $ret is also in IR scope; it's a word
      putIRVarType "$ret" tword
      --The memory state variable $mem is necessary for tracking dependency
      --on memory side effects.
      putIRVarType "$mem" Mem
      mapM_ seqS body
      --There's always an implicit return at the end of a function body,
      --returning a null value.
      --Todo deduplicate so I don't accidentally miss adding new virtual state
      --params (storage etc) when I modify return in seqS.
      zws <- askReturnType >>= nullValue
      emit $ IR1.Return () $ ["$mem","$ret"] ++ zws

      return arity
    _ -> throwE $ BadFunctionType f ft

--Args: Pattern, C type of rhs, words of rhs.
--The same logic can be used for pattern-matching in function lhses as in
--assignment.
--Word assignment should copy; then seqE x can just return (t,[x#1..x#n])
--if x : t.
--Weird edge case: global names in a function lhs.
patternMatch :: Pat -> T -> [Name] -> Seq ()
patternMatch p t ws =
  --TODO add globals, *e, p.field, e[e]
  case p of
    PWild -> return ()
    PVar x -> do
      ni <- getCNameInfo x
      --Note constructors are syntactically prevented from being pattern vars
      case ni of
        IsFunction _ -> throwE $ Can'tAssignToFunction x
        IsPrimFun -> throwE $ Can'tAssignToPrimFun x
        --The variable is already in scope
        --Need to do variable coercion so x : Word = 3 works
        IsLocal t' -> do
          cws <- softCoerce t' t ws
          assign x cws
        --The variable is free, so we'll accept any type and add the var to the
        --C scope.
        IsUnbound -> do
          putCLocalVarType x t
          assign x ws
    --{p1,p2} = s => p1 = select 1 s, p2 = select 2 s...
    --{field: p} = s => p = s.field
    PStruct fs ->
      error "TODO"
    --Like pstruct {x,y,z}, but requires t is a tuple
    PTup ps ->
      case unTupleT t of
        Nothing -> throwE $ PTupNonTuple ps t
        Just ts
          | length ps /= length ts -> throwE $ PTupLengthMismatch ps ts
          | let -> do
              twss <- splitTuple ts ws
              sequence_ [patternMatch p t ws
                        | (p,(t,ws)) <- zip ps twss]
    --TODO add PHash (:# for patterns)
    --What p's are valid for p.field* = e?
    --_.field* = e should reasonably just be a noop (though no sane programmer
    --would write that)
    PDot p field -> do
      let (p',nmixs) = unrollPFields (PDot p field)
      case p' of
        PWild -> return ()
        PVar nm -> do
          ni <- getCNameInfo nm
          let ge = throwE $ GenericError $
                "Bad name info for struct.field* = e :" ++
                show (nm,ni,nmixs)
          case ni of
            IsLocal structT -> setStructLocal nm structT nmixs t ws
            IsFunction _ -> ge
            IsPrimFun -> ge
            IsUnbound -> throwE $ GenericError $
              "You can't assign fields of unbound vars: " ++ show (nm,nmixs)
        --Adding proper ptr.field* = e implementation now...
        --To use:
        --genStore structSz leftPad fieldSz rightPad off ptr ws
        Deref ptr -> do
          (ptrt,ptrws) <- seqE ptr
          case ptrt of
            Ptr r struct ->
              let [ptrw] = ptrws in
              --Only memory, storage and tstorage can be mutated
              case r of
                Memory -> do
                  --Copied from setStructLocal
                  ixs <- indicesAndNamesToIndices nmixs struct
                  (fieldT,sz,off,pl,pr) <- fieldsInfo ixs struct
                  szStruct <- numBitsT struct

                  ws' <- softCoerce fieldT t ws
                  genStore szStruct pl sz pr off ptrw ws'
                _ -> throwE $ GenericError $ "*ptr.field* assignments "
                  ++ "unsupported for region " ++ show r ++ " atm"
          {-do
          --Need two faux locals to prevent reevaluation of the ptr expr...
          fauxS <- newAnonVar
          fauxP <- newAnonVar
          seqS (PVar fauxP := ptr)
          seqS (PVar fauxS := (Var "deref" :$ Var fauxP))
          structT <- do
            ni <- getCNameInfo fauxS
            case ni of
              IsLocal t -> return t
              _ -> error "This should never happen."
          setStructLocal fauxS structT nmixs t ws
          seqS (Deref (Var fauxP) := Var fauxS)
        _ -> throwE $ GenericError $
             "Bad pattern for .field* = e: " ++ show (p',nmixs)
-}
    --TODO improve error message
    Deref ptr -> do
      (pt,pws) <- seqE ptr
      case pt of
        Ptr r a -> do
          let [pw] = pws
          ws' <- softCoerce a t ws
          let imm r = throwE $ GenericError $ "Can't write to a pointer to " ++
                "an immutable region: " ++ show (ptr,r)
          case r of
            Memory -> assignPtr pw a ws'
            --TODO storage, tstorage
            Calldata -> imm r
            Code -> imm r
            Returndata -> imm r
            _ -> throwE $ GenericError
                 "Other regions unsupported for ptr assignment atm"
        _ -> throwE $ GenericError "Can't assign to non-pointers"
unrollPFields :: Pat -> (Pat,[Either Name Int])
unrollPFields p = let (p',nmixs) = go p
                  in (p',reverse nmixs)
  where go (PDot p field) =
          let (p',nmixs) = go p
          in (p',Left field : nmixs)
        go p = (p,[])
{-
--Used in hacky, unoptimized version of *ptr.field* = e
rollPFields :: Pat -> [Either Name Int]
rollPFields p =
  let r = rollPFields
  in \case
    [] -> p
    f:fs ->
      case f of
        Left nm -> r (PDot p nm) fs
        Right ix -> r (PHash p ix) fs
-}
--The word-level implementation of selecting the nth struct field of a struct
--(represented as words on the stack).
--T, [Name] is the struct type and its on-stack repr
--If it's not a struct type, fail.
structSelect :: Int -> T -> [Name] -> Seq (T,[Name])
structSelect = undefined

--Given a number of words equal to t's word size, coerces them to t
coerceT :: T -> [Name] -> Seq [Name]
coerceT t ws = do
  n <- numWordsT t
  if n /= length ws
    then error "Compiler error: word length mismatch in coerceT"
    else sequence [coerceIRT (W i t) w | (i,w) <- zip [1..] ws]
--Coerces a single IR var to a new anon var
coerceIRT :: IRT -> Name -> Seq Name
coerceIRT t w = do
  v <- newAnonVar
  emitOp [(v,t)] Copy [w]
  return v
                                     
--TODO refactor other instances of this pattern to anonVarsT
anonVarsT :: T -> Seq [Name]
anonVarsT t = do
  n <- numWordsT t
  mapM (\n -> do
           v <- newAnonVar
           putIRVarType v (W n t)
           return v) [1..n]

--The scope is reset at the end
seqBlock :: Block -> Seq [IR]
seqBlock irs = snd <$> isolate (mapM seqS irs)
--For now, support only assignment to x. Later: tuple
--For now, no tail call support
seqS :: S -> Seq ()
seqS = \case
  p := e -> do
    (t,ws) <- seqE e
    patternMatch p t ws
  --The last argument of any function is $ret : tword
  --The first value to return (and the first result of any call) is $mem
  --The second is $ret!
  --State variables in return should not affect the stack target.
  --TODO add tail call support for return f(args), where f is not a primfun.
  --Note: expressions may modify $mem, but seqE should never return it.
  DTs.Return e -> do
    t <- askReturnType
    (t',ws) <- seqE e
    cws <- softCoerce t t' ws
    emit $ IR1.Return () $ ["$mem","$ret"] ++ cws
  --Applies truthy to e, returning one word
  --Complication: what are the scope rules for the e in ifte? The same as
  --the block it's contained in... meaning an assignment in e will carry over
  --to cont.
  DTs.Ifte e bthen belse -> do
    v <- truthyE e
    t <- seqBlock bthen
    e <- seqBlock belse
    emit $ IR1.Ifte () v t e
  --This one's tricky... the e is within the parent scope, but like seqBlock
  --you don't want to emit it directly.
  --Simple rule: new assignments in e will not be visible in the body or the
  --end of the while. Declarations in exprs are ugly anyway, don't support
  --them... they interact poorly with && and _?_:_
  DTs.While e body -> do
    (v,pre) <- isolate $ truthyE e
    post <- seqBlock body
    emit $ IR1.While () pre v post
--You need to know the *word* vars returned to use them;
--if $mem is involved it remains the same.
--Also returns the type (which only depends on global info, locals and
--subexprs); type checking is fused into IR codegen to avoid recomputing it
--wherever it's relevant in codegen.

--Isolate the effect of running a Seq in order to insert it into a control
--structure like Ifte or While.
--anonVarCounter is passed on, but the other state is not. Writer output is
--suppressed and instead returned. Exceptions are propagated.
--Now we must also pass on anonLabelCounter, anonStaticData
isolate :: Seq a -> Seq (a,[IR])
isolate m = do
  s <- get
  (a,irs) <- censor (const []) $ listen m
  s' <- get
  put s{anonVarCounter = anonVarCounter s',
        anonLabelCounter = anonLabelCounter s',
        anonStaticData = anonStaticData s'
        }
  return (a,irs)

allocAnonLabel :: Seq Name
allocAnonLabel = do
  --Do I already have a function to get the current function's name...?
  Defun fnm _ _ _ <- seqrFunction <$> ask
  s <- get
  let n = anonLabelCounter s
      label = fnm ++ ".static#" ++ show n
  put s{anonLabelCounter = n+1}
  return label
prependAnonStaticData :: Static -> Seq ()
prependAnonStaticData static = do
  s <- get
  put s{anonStaticData = static : anonStaticData s}

seqE :: E -> Seq (T,[Name])
seqE = \case
  --integer literals may be at most one word
  EInteger n -> do
    let t = typeOfInteger n
    v <- pushK t (Const n)
    return (t,[v])
  --Allocates a new label fname.static#n which will point to the string;
  --returns (ptr :: Ptr Code Byte,len :: UInt 16)
  --Fails if any char has a code point > 255
  EString str ->
    let bs = map ord str
    in if any (>255) bs
       then throwE $ GenericError $ "Non-UTF8 string in seqE: " ++ str
       else do
      sptr <- allocAnonLabel
      prependAnonStaticData $ (UInt 8, map Right bs)
      ptr <- pushK (Ptr Code (UInt 8)) (LabelConst sptr)
      len <- pushK (UInt 16) ((Const $ fromIntegral $ length bs))
      --Issue: do I need to coerce ptr and len here?
      return (Pair (Ptr Code (UInt 8)) (UInt 16), [ptr,len])
  --For now, it's either a user function, local or undefined
  --locals can't shadow functions
  Var nm -> do
    ni <- getCNameInfo nm
    case ni of
      IsFunction t -> do
        v <- pushK t (LabelConst nm)
        return (t,[v])
      IsLocal t -> do
        --The number of words is determined by t... but it won't be a pure fun
        --once user-defined types are supported.
        n <- numWordsT t
        --For now, all vars in scope must also already be assigned, since they
        --enter scope on assignment.
        --A use of a var is not a noop, it's a renaming. The difference is
        --a subsequent assignment to the original var won't affect the
        --renamed one.
        ws <- sequence [copyVar (W i t) (nm ++ "#" ++ show i)
                       | i <- [1..n]]
        return (t,ws)
      IsUnbound -> throwE $ UnboundVar nm
      _ -> error $ "Compiler error: unexpected ni in seqE (Var) " ++ show(ni,nm)
  --Two cases: f is a primfun or an ordinary expr.
  --For now, primfuns can only be fully applied, making them akin to syntactic
  --constructs. Since standalone primfuns would need to be monomorphized,
  --perhaps make that permanent.
  --Infix application a + b => +(a,b), i.e. + is applied to a single tuple.
  --The same name in source may compile to different primfun names at this
  --level; consider *_ (deref) and _*_ (multiplication).
  --But for now I'll just look at the argument type and form to dispatch.
  --Note you can't always eval the arg first; consider a && b.
  --Primfun names may neither be assigned nor defined to, so I don't need to
  --worry about shadowing.
    
  --Simple primfuns, no short-circuiting:
  Var pf :$ x
    | Just scheme <- M.lookup pf simplePFs -> do
        (tx,wsx) <- seqE x
        scheme tx wsx
  --Ordinary (proper) function application; Args: $mem,f,argws
  --Potential future feature: support for a closure type.
  f :$ x -> do
    (tf,wsf) <- seqE f
    case tf of
      a :-> b -> do
        let [wf] = wsf
        (tx,wsx) <- seqE x
        args <- softCoerce a tx wsx
        --alloc n anon vars, where n is b's word size
        --emit vars = call [$mem,f,args]
        --return type: b
        n <- numWordsT b
        retws <- replicateM n newAnonVar
        let retts = [W m b | m <- [1..n]]
        --We thread $mem through calls, but it's not part of the expr's
        --word output.
        --Stack layout before jump: wf,args,ret.
        --Note: the IR does not include the ret argument!
        emitOp (("$mem",Mem):zip retws retts) Call ("$mem":wf:args)
        return (b,retws)
      _ -> throwE $ ApplicationToNonFunction f tf
  --The fields are concatenated, with the field values emitted in reverse
  --order.
  EStruct padnmes -> do
    padnmtws <- mapM (\((pad,al),mnm,e) -> do
                         (t,ws) <- seqE e
                         return ((pad,al),mnm,t,ws)) padnmes
    buildStruct padnmtws
  --In future, I may add new uses of .field beyond struct, such as
  --n.slice(a,b)
  --Structs with duplicate field names should arguably be forbidden, but I
  --don't need to check for them here; do so in kind check (TODO) and
  --on struct creation.
  e :. field -> handleIndexing (e :. field)
  e :# n -> handleIndexing (e :# n)
  --Simple hard coercion: if e is longer than the target type, truncate it;
  --if it's shorter, zero-pad it. Ignore internal padding.
  Coerce targetT e -> do
    (sourceT,ws) <- seqE e
    targetBits <- numBitsT targetT
    --Why misleading? Because the value might include left-padding we don't
    --need to mask
    misleadingSourceBits <- numBitsT sourceT
    lp <- leftPadding sourceT
    --This is the number we care about
    let sourceBits = misleadingSourceBits - lp
        targetWords = (targetBits `roundedUpMod` 256) `div` 256
        sourceWords = (sourceBits `roundedUpMod` 256) `div` 256
    case () of
      --No masking needed; just copy the lowest words from ws
      _ | targetBits >= sourceBits -> do
            --Avoiding redundant computation at cost of complexity
            let 
            --Will be optimized away if unused
            (z,_) <- runEDSL $ word 0
            let paddedWs = replicate (targetWords-sourceWords) z ++
                           ws
            --We adjust the IR types for readability
            retypedWs <- mapM (\(irt,w) ->
                                 fst <$> (runEDSL $ coerce irt (EVar w))) $
                         zip [W n targetT | n <- [1..]] paddedWs
            return (targetT,retypedWs)
        --We must mask the top word of the target words if there are any
        --If targetT is a whole number of words, that has no runtime impact
        | targetBits == 0 ->
          return (targetT,[])
        | let -> do
            --The target words before truncation and coercion; taken from the
            --bottom words of the source
            let leftmost:rest = drop (targetWords-sourceWords) ws
            (maskedLeftmost,_) <- runEDSL $ mask (targetBits `mod` 256) $
                                  EVar leftmost
            retypedWs <- mapM (\(irt,w) ->
                                 fst <$> (runEDSL $ coerce irt (EVar w))) $
                         zip [W n targetT | n <- [1..]] (maskedLeftmost:rest)
            return (targetT,retypedWs)
  --Implementation (Con (arg :: argT) (allocPtr :: Ptr r Byte)):
  --Each constructor has type arg -> TyCon params, where arg and params may
  --contain free vars.
  --actualParams <- subst params given (argT,r) =:= (arg,firstParam)
  --rett = TyCon actualParams
  --retPtr <- copy allocPtr :: rett
  -- *(allocPtr :: Ptr r {Byte,argT}) = {tag_Con,arg}
  --allocPtr += <1 + sizeof arg>
  --return (rett,retPtr)
  Con con arg allocPtrPat -> do
    ptrE <- pat2e con allocPtrPat
    --To both check the pointer has an appropriate type and use it, we must
    --save it to a faux C var
    fauxPtr <- newAnonVar
    seqS (PVar fauxPtr := ptrE)
    ni <- getCNameInfo fauxPtr
    let IsLocal ptrT = ni
    case ptrT of
      Ptr r (UInt 8)
        | not $ r `elem` [Memory,Storage,TStorage] ->
          throwE $ GenericError $
          "Alloc ptr for " ++ con ++ " points into an immutable region " ++
          show r
        | let -> do
            --Get the constructors tag byte, (polymorphic) arg type and
            --return type. The return type is split into tycon, region
            --parameter and the remaining params to make 0-arity tycons
            --non-representable and ease unification of the region param with
            --r.
            --Note unification is local; the type system is not Hindley-Milner.
            (tagCon,conArgT,tycon,rt,remParams) <- getConInfo con
            let tagConE = EInteger $ fromIntegral tagCon
            --Because I don't separate type inference from compilation, I
            --need to save {tag,arg} to a new faux C var before I can check
            --the arg is actually a valid argument.
            faux <- newAnonVar
            seqS (PVar faux := structE [tagConE,arg])
            --Now we retrieve the arg's type...
            ni <- getCNameInfo faux
            let IsLocal structT@(Struct [_,(_,_,argT)]) = ni
            case bindT (Pair conArgT $ TyVar rt) (Pair argT r) of
              Left err -> throwE $ GenericError $
                "Bind failure in " ++ con ++ " allocation: " ++ show err
              Right v2t -> do
                --Instantiate the datatype
                --Note we check arg and alloc pointer contain enough info to
                --determine the datatype's params once per datatype; we don't
                --need to do so here.
                let datatype = foldr (flip (:$$)) (TyCon tycon) $
                               map (v2t M.!) $ rt:remParams
                --Now we write the struct to the pointer:
                --(*(fauxPtr :: Ptr r structT)) = faux
                seqS (Deref (Coerce (Ptr r structT) $ Var fauxPtr) :=
                      Var faux)
                --We bump allocPtr by sizeof structT:
                --This works becuase fauxPtr is a byte ptr
                sz <- numBytesT structT
                seqS (allocPtrPat := (Var "+" :$
                                      tupleE [Var fauxPtr,
                                              EInteger $ fromIntegral sz
                                             ]))
                --fauxPtr now holds the original ptr to return coerced to
                --datatype:
                seqE (Coerce datatype $ Var fauxPtr)
      _ -> throwE $ GenericError $
        "Alloc ptr for " ++ con ++ " must be a byte ptr, but instead it's "
        ++ show ptrT
      
--pat2e pat returns e if the given pattern unambiguously corresponds to
--the expression e.
--Example: foo.bar is an unambigous pattern as long as foo is bound.
--Note type errors may be thrown when you try to evaluate the expression;
--for example, foo may not have the field bar.
--It's in Seq to check if locals are bound and to immediately throw an
--error if it encounters an unbound one.
pat2e :: Name -> Pat -> Seq E
pat2e con = go
  where
    go :: Pat -> Seq E
    go = \case
      PVar nm -> do
        ni <- getCNameInfo nm
        case ni of
          IsLocal t -> return $ Var nm
          _ -> throwE $ GenericError $
               con ++ ": Bad name info for var " ++ nm ++ " in pat2e: " ++
               show ni
      PTup ps -> tupleE <$> mapM go ps
      PDot p field -> (:. field) <$> go p
      PHash p ix -> (:# ix) <$> go p
      Deref e -> return $ Var "deref" :$ e
      p -> throwE $ GenericError $
           con ++ ": Pattern does not unambigously correspond to an expr: "
           ++ show p
                           
unrollEFields :: E -> (E,[Either Name Int])
unrollEFields = (id *** reverse) . go
  where go = \case
          e :. field -> (id *** (Left field:)) $ go e
          e :# ix -> (id *** (Right ix:)) $ go e
          e -> (e,[])
--Opt: convert *ptr.field* to a deref of a pointer to the field if the field
--is byte-aligned.
handleIndexing e = do
  --First I unroll all the nested accesses
  let (struct,nmixs) = unrollEFields e
  case struct of
    Var "deref" :$ ptr -> do
      (ptrT,ptrWs) <- seqE ptr
      case ptrT of
        --Generalized *ptr slice: the field need not be byte aligned or padded.
        --In contrast to simple *ptr, there may be nonzero bits in the same
        --byte as the field.
        Ptr r a -> do
          ixs <- indicesAndNamesToIndices nmixs a
          (fieldT,szField,offField,lpField,_) <- fieldsInfo ixs a
          szStruct <- numBitsT a
          let ptrW = case ptrWs of
                       [p] -> p
                       _ -> error $ "Compiler error: ptr has wrong number of "
                            ++ "words in handleIndexing: " ++ show (ptr,ptrWs)
          comment "Dereferencing *ptr.field:"
          comment $ "(szStruct,lpField,szField,offField): " ++
            show (szStruct,lpField,szField,offField)
          resWs <- genDeref r szStruct lpField szField offField ptrW
          return (fieldT,resWs)
          --genDerefMem structSz leftPad fieldSz off ptr
        _ -> throwE $ GenericError $
          "Non-pointer in *e.field*: " ++ show (ptr,ptrT)
    _ -> do
      (structT,structWs) <- seqE struct
      getStructFields structT structWs nmixs
{-
  ixs <- indicesAndNamesToIndices fieldIxs t
  --Return type, its size, offset in the struct, left and right-padding
  --We don't need right-padding, so we ignore it.
  (tRes,szRes,offRes,lpRes,_) <- fieldsInfo ixs t
-}

--The compilation schemes for simple primfuns (where their argument is evaluated
--normally rather than short-circuited).
--Badargs should lead to a Seq exception.
simplePFs :: Map Name (T -> [Name] -> Seq (T,[Name]))
simplePFs = M.fromList [
  --Mathops
  --C has unary +, but it's pretty vestigial... I'll just ignore it
  --TODO add Ptr r a + Int {}
  ("+",\t ws ->
      case (t,ws) of
        (Pair t1@(Int s1 len1) t2@(Int s2 len2),[w1,w2]) ->
          pfMathOp "add" t1 t2 (w1,w2)
        --ptr_a + n => ptr + sizeof(a) * n
        (Pair (Ptr r a) (Int s len), [wptr,wn]) -> do
          sz <- numBytesT a
          off <- wop2 "mul" (wword sz) (return wn)
          ptr' <- wmask 16 $ wop2 "add" (return off) (return wptr)
          return (Ptr r a, [ptr'])
        _ -> throwE $ BadArgPrimFun "+" t),
  --Recall: mul/smul, div/sdiv need special treatment
  --Binary bitwise ops
  ("&", binaryBitOp "&" "and" False),
  ("|", binaryBitOp "|" "or" True),
  ("^", binaryBitOp "^" "xor" True),
  --Pointer derefence
  ("deref",derefPtr),
  --Branching primfuns; they can be simple because the IR is unaware of
  --branching, it's the CFG phase that handles that.
  --evm_return(Ptr Memory a, Int {}) : ()
  ("evm_return",\t ws ->
      case (t,ws) of
        (Pair (Ptr Memory a) (UInt blen), [p,len]) -> do
          emit $ EVM_RETURN () "$mem" p len
          return (Struct [], [])
        _ -> throwE $ BadArgPrimFun "evm_return" t),
  --Generic copy operation, to integrate all *copy instructions except
  --extcodecopy:
  --m, calldata, code, returndata
  --copy(pto,pfrom,n) copies n elements from pfrom to pto; takes into account
  --the bytesize of *pto and *pfrom, which must be equal
  --TODO: optimize *memptr = *ptr to copy(memptr,ptr,1)
  ("copy", \t ws ->
      case t of
        Triplet (Ptr Memory a) (Ptr r a') nt
          | a == a' -> do
              let [pto,pfrom,nw] = ws
              nws <- softCoerce (UInt 16) nt [nw]
              let [n] = nws
              bytesz <- numBytesT a
              tot <- runEDSLW $ mulK bytesz (EVar n)
              case r of
                Memory ->
                  emitOp [("$mem",Mem)] (Opcode "mcopy")
                    ["$mem",pto,pfrom,tot]
                Code -> emitOp [("$mem",Mem)] (Opcode "codecopy")
                  [pto,pfrom,tot]
                _ -> error $ "Compiler error: todo in copy " ++ show r
              return (Struct [], []))
  ]
--Pointer type, pointer word (singular) -> *ptr
--All regions are byte-addressed starting from 0; all values stored in a
--region are byte-padded, with their first byte starting at address p.
--That means a uint16 at 0 must be left-shifted by 240 before mstoring and
--right-shifted on mload.
--For now, mloads touch memory so their order is strict. To ensure multi-word
--values are loaded in the stack order used in calling conventions, you
--must load words from the right.
--deref of a 33-byte value at ptr becomes mload(ptr+1), mload(ptr) >> 8*31
--Generalizing: n*32 + modulus at ptr becomes mload(ptr+modulus+32*i), i <-
--n-1 to 0, mload(ptr) >> 8*(32-modulus)
--Calldata follows the same logic.
--Storage deref has two cases: the byte sequence either requires an additional
--SLOAD due to overlapping a slot boundary or not.
--Worst-case scenario: 2-byte load, two SLOADs.
--Code ptr deref could be implemented using scratch memory... but I need
--array globals first.
--A minimum of 32B would be practical.
derefPtr :: T -> [Name] -> Seq (T,[Name])
derefPtr (Ptr r a) [w] = do
  sz <- (`roundedUpMod` 8) <$> numBitsT a
  ws <- case r of
          Memory -> derefMem mload sz w
          Calldata -> derefMem calldataload sz w
          Storage -> error"Compiler error: derefPtr storage not supported yet"
          TStorage -> error"Compiler error: derefPtr tstorage not supported yet"
          _ -> throwE $ GenericError $ "Region does not support deref: " ++
               show r
  ws' <- coerceValue a ws
  return (a,ws')
derefPtr t ws = throwE $ GenericError $ "Badarg to *_ : " ++ show (t,ws)
--TODO give more appropriate name since it's now also used for calldata
--sz is the byte size of the (byte-padded) value
derefMem :: (Name -> Seq Name) -> Int -> Name -> Seq [Name]
derefMem load sz ptr = do
  let nbytes = sz `div` 8
      modulus = nbytes `mod` 32
      remwords = nbytes `div` 32
  
  --Note: ptr + k may extend beyond the normal 16b range of a pointer;
  --then &(ptr->field) will overflow. Solution: just don't get near the
  --wraparound boundary.
 
  --The simplest case. Load ptr, ptr + 32, ... in reverse order.
  --Return them in original order.
  wholeWords <- reverse <$>
                (sequence $
                 reverse [do (ptr',_) <- runEDSL $ addK (fromIntegral n)
                                         (EVar ptr)
                             load ptr'
                         | n <- map (+ modulus) [0,32..32*(remwords-1)]
                         ])
  if modulus > 0
    then do
    w <- load ptr
    (partialWord,_) <- runEDSL $ shift (8*modulus - 256) $ EVar w
    return (partialWord:wholeWords)
    else return wholeWords

--Bit-padding is now deprecated; TODO simplify ptr->field* get and put.
--If mask of the top word is necessary, it can be done by left-shifting before
--right-shifting (cost: 6 gas, 3 bytes).
--Struct size, left padding in the struct, field size and offset are all
--in bits.
--The first byte of the struct starts at ptr; if structSz % 8 == 0 then it
--contains 8 struct bits, otherwise structSz % 8. It has 8 - that bits of
--padding.

--Cases where m > 0:
--partial ends before the last byte of mload ptr: shl, shr
--it ends at last byte: mask
--it ends afterwards: mload (ptr+k), shr
--I'd actually ignored region entirely in ptr->field*; I need to disallow
--derefs to code and returndata (which don't support loading to the stack
--without a memory side effect). TODO merge with derefPtr, support storage
--and tstorage access.
genDeref :: T -> Int -> Int -> Int -> Int -> Name -> Seq [Name]
genDeref r structSz leftPad fieldSz off ptr
  | r `elem` [Code,Returndata] =
    throwE $ GenericError $ "Non-loadable region in genDeref: " ++ show r
  | fieldSz == 0 = return []
  --The byte-addressed regions
  | r `elem` [Memory,Calldata] = do
      let structBs = (structSz `roundedUpMod` 8) `div` 8
          fieldBs = (fieldSz `roundedUpMod` 8) `div` 8
          offBs = off `div` 8
          --The field's byte offset from ptr
          leftOff = structBs - (offBs + fieldBs)
          --The byte size of the partial word if nonzero
          m = fieldBs `mod` 32
          --The number of whole words
          d = fieldBs `div` 32
          load = if r == Memory then mload else calldataload
      comment $ "(structBs,fieldBs,offBs,leftOff,m,d): " ++
        show (structBs,fieldBs,offBs,leftOff,m,d)
      partial <- if m > 0
                 then let lastByte = leftOff + m - 1
                      in case () of
                           --shl (TODO opt away if leftPad sufficient),
                           --shr
                           _ | lastByte < 31 -> do
                                 comment $ "lastByte: " ++ show lastByte
                                 comment "shl, shr"
                                 w <- load ptr
                                 p <- runEDSLW $
                                      shift (8*(m-32)) $
                                      shift (8*leftOff) $ EVar w
                                 return [p]
                             --partial word ends at last byte of mload ptr;
                             --use and to mask
                             | lastByte == 31 -> do
                                 w <- load ptr
                                 p <- runEDSLW $ mask (8*m) $ EVar w
                                 return [p]
                             --we need to mload off (ptr+k) anyway; load
                             --off ptr+leftOff and shr
                             | let -> do
                                 ptr' <- runEDSLW $ addK leftOff $ EVar ptr
                                 w <- load ptr
                                 p <- runEDSLW $ shift (8*(m-32)) $ EVar w
                                 return [p]
                 else return []
      wholeWords <- mapM (\offset -> do
                             ptr' <- runEDSLW $ addK offset $ EVar ptr
                             load ptr')
                    [32*i + leftOff + m | i <- [0..d-1]]
      return $ partial ++ wholeWords
  | r `elem` [Storage,TStorage] = error "TODO support genDeref (sto/tso)"
{-
  | let = do
          --First, fetch the bytes which contain any field bits
          let --Offset from right
              rightByteOff = off `div` 8
              leftByteOff = (off+fieldSz-1) `div` 8
              fieldBs = leftByteOff - rightByteOff + 1
              structBs = (structSz `roundedUpMod` 8) `div` 8
              --The byte index from left at which the field starts
              offFromLeft = structBs - 1 - leftByteOff
          (rshHead,ws) <- derefBytes offFromLeft fieldBs ptr
          let offBits = off `mod` 8
              w:ws' = ws
          --If the field is byte-aligned everything is much simpler:
          if offBits == 0
            then do
            --Just shift and mask the top word:
            --It has sz % 256 relevant bits at offset 8*rshHead
            --Right-padding isn't relevant; we're going to right-shift it
            --to offset 0 anyway.
            w' <- sliceWord leftPad (fieldSz `mod` 256) (8*rshHead) 0 0 w
            return $ w':ws'
            else do
            --This is the tricky bit
            --The number of unique bits in the first input word:
            let ubits = (fieldSz + offBits) `mod` 256
            --The output of the top word (may be [] if it's consumed by
            --right-shift) and the bits to be or'd with the next word.
            (top,topL) <- if ubits > offBits
                          then do
              w' <- sliceWord leftPad (ubits - offBits)
                (8*rshHead + offBits) 0 0 w
              topL <- sliceWord 0 offBits (8*rshHead) 0 (256 - offBits) w
              return ([w'],topL)
                          else do
              --I'm not making use of the field's right-pad...
              topL <- sliceWord leftPad ubits (8*rshHead) 0 (256 - offBits) w
              return ([],topL)
            --The bits to be shifted to the right (computed from all words
            --but the last)
            --That means the lowest offBits bits shifted all the way to the
            --left (requiring only a shl).
            ls <- (topL:) <$> mapM
              (sliceWord 0 offBits 0 0 (256-offBits)) (init ws')
            rs <- mapM (sliceWord 0 (256-offBits) offBits 0 0) ws'
            --The lower output words: ls | rs
            bot <- zipWithM (\l r -> runEDSLW $ EVar l .| EVar w) ls rs
            return (top ++ bot)
-}
--ptr->field* = v implementation function, now assuming byte-aligned fields
--rightPad matters iff fieldSz < 256: then if left pad + field + right pad add
--up to >=32 bytes you can shl and mstore.
--If field bytes >= 32, you don't need to write back.
--If field sz == 0, store is a noop.
--If field byte sz = 1, use an mstore.
genStore :: Int -> Int -> Int -> Int -> Int -> Name -> [Name] -> Seq ()
genStore structSz leftPad fieldSz rightPad off ptr ws = do
  let structBs = (structSz `roundedUpMod` 8) `div` 8
      fieldBs = (fieldSz `roundedUpMod` 8) `div` 8
      offBs = off `div` 8
      --The field's byte offset from ptr
      leftOff = structBs - (offBs + fieldBs)
      --The byte size of the partial word if nonzero
      m = fieldBs `mod` 32
      --The number of whole words
      d = fieldBs `div` 32
  case () of
    _ | fieldBs == 0 -> return ()
      | fieldBs == 1 -> do
          let [w] = ws
          ptr' <- runEDSLW $ addK leftOff $ EVar ptr
          mstore8 ptr' w
      | fieldBs >= 32 -> do
          --If the field has a partial word, shl it by 8*(32-m) and
          --mstore it to ptr+leftOff. mstore the remaining d whole words to
          --ptr+leftOff+m.
          --If m == 1, you can mstore8 instead of shifting.
          wholes <- case () of
                      _ | m == 0 -> return ws
                        | m == 1 -> do
                            let hd:tl = ws
                            ptr' <- runEDSLW $ addK leftOff $ EVar ptr
                            mstore8 ptr' hd
                            return tl
                        | let -> do
                            let hd:tl = ws
                            ptr' <- runEDSLW $ addK leftOff $ EVar ptr
                            hd' <- runEDSLW $ shift (8*(32-m)) $ EVar hd
                            mstore8 ptr' hd'
                            return tl
          mapM_ (\(offset,w) -> do
                    ptr' <- runEDSLW $ addK offset $ EVar ptr
                    mstore ptr' w) $
            zip [32*i + leftOff + m | i <- [0..d-1]] wholes
      --This is the trickiest bit: the field is smaller than a word, so
      --padding matters.
      --If left-padding bytes + field bytes >= 32, just mstore
      --If left+field+right >= 32, shl and mstore
      --For now just use a simple, suboptimal implementation:
      --mstore (ptr+leftOff) (w << (8*(32-m)) |
      --                      mload (ptr+leftOff) & mask (8*(32-m)))
      | let -> do
          let [w] = ws
          ptr' <- runEDSLW $ addK leftOff $ EVar ptr
          old <- mload ptr'
          new <- runEDSLW $
            let oldSz = 8*(32-m)
            in shift oldSz (EVar w) .| mask oldSz (EVar old)
          mstore ptr' new
              
--A vital combinator for genDeref:
--sliceWord lp sz off rp lsh {_,0:lp,field:sz,0:rp,_} = field << lsh,
--implemented as efficiently as possible.
--Note the padding lp and rp may extend beyond the bounds of the word.
sliceWord :: Int -> Int -> Int -> Int -> Int -> Name -> Seq Name
sliceWord lp sz off rp lsh w
  | any (<0) [lp,sz,off,rp,lsh] ||
    sz + off > 255
  = error $
    "Compiler error: badarg in sliceWord: " ++ show (lp,sz,off,rp,lsh)
  --This isn't expected to happen, but I'll handle it anyway:
  | sz == 0 = fst <$> runEDSL (word 0)
  | sz == 256 = return w
  | let = let cleanLeft = sz + lsh + lp > 255
              cleanRight = lsh - rp <= 0
              --cleanLeft means any garbage to the left is shifted out,
              --analogously for cleanRight
              offMask = word ((2^sz - 1) * 2^off) & EVar w
          in case () of
               --If there is no need for masking, just shift
               _ | cleanLeft && cleanRight ->
                   runEDSLW (shift (lsh-off) $ EVar w)
                 --If there is no need for shifting, any masking must be
                 --done with and.
                 | lsh == off ->
                   runEDSLW offMask
                 --If only one of left or right is dirty, you can mask it by
                 --shifting (which has the same gas cost but smaller code).
                 --Otherwise you need to use and; when shifting left it's better
                 --to do that first.
                 | otherwise ->
                   case () of
                     _ | not (cleanLeft || cleanRight) ->
                         runEDSLW (shift (lsh-off) offMask)
                       | cleanLeft ->
                         runEDSLW $ shift lsh $ shift (-off) $ EVar w
                       --cleanRight && not cleanLeft;
                       --Shift the field as far left as possible, then shr to
                       --the final position
                       | let ->
                         let leftShift = 255 - (off + sz - 1)
                         in runEDSLW $ shift (lsh - leftShift) $
                            shift leftShift $ EVar w
--Fetches bs bytes at offset off from ptr, but does not handle masking the
--partial word.
--Instead, reports by how many bytes the top word must be right-shifted.
--Ex: derefBytes 0 33 ptr => (31,(mload ptr, mload (ptr+1)))
--If rsh > 0 and bs > 32, the top word contains rsh bytes duplicated from the
--next word.
derefBytes :: Int -> Int -> Name -> Seq (Int,[Name])
derefBytes off bs ptr
  | off < 0 = error $ "Negative offset in derefBytes: " ++ show (off,bs,ptr)
  | bs < 0 = error $ "Negative byte count in derefBytes: " ++ show (off,bs,ptr)
  | let = do
          let r = bs `mod` 32
              n = bs `div` 32
              wholeWords = [do (ptr',_) <- runEDSL $ addK (off + r + 32*i)
                                           (EVar ptr)
                               mload ptr'
                           | i <- [0..n-1]
                           ]
          ws <- reverse <$> sequence (reverse wholeWords)
          (rsh,p) <- loadPartial r
          return (rsh,p ++ ws)
            where
              loadPartial 0 = return (0,[])
              loadPartial r =
                let cr = 32 - r --num 0 bytes of the partial word
                in if cr >= off
                   then do (ptr',_) <- runEDSL $ addK (fromIntegral (off-cr))
                                       (EVar ptr)
                           w <- mload ptr'
                           return (0,[w])
                   else do w <- mload ptr
                           return (cr-off,[w])
--($mem,result) = mload ($mem,addr)
--TODO first tree shake away unused mloads, then force the next write to be
--placed after all remaining ones.
--Doesn't fit in EDSL because it manipulates a specific var, $mem.
--TODO use EDSL anyway, allow memory regions other than a
--single global one ($mem) to be passed.
mload :: Name -> Seq Name
mload addr = do
  res <- newAnonVar
  emitOp [("$mem",Mem),(res,tword)] (Opcode "mload") ["$mem",addr]
  return res
mstore :: Name -> Name -> Seq ()
mstore addr val = do
  emitOp [("$mem",Mem)] (Opcode "mstore") ["$mem",addr,val]
  return ()
mstore8 :: Name -> Name -> Seq ()
mstore8 addr val = do
  emitOp [("$mem",Mem)] (Opcode "mstore8") ["$mem",addr,val]
  return ()
calldataload :: Name -> Seq Name
calldataload addr = do
  res <- newAnonVar
  emitOp [(res,tword)] (Opcode "calldataload") [addr]
  return res
  
--Implements *ptr = v, which is a special case of *ptr#ix* = v and much simpler
--to implement.
--All values in memory are byte-aligned, so a value which isn't a whole number
--of bytes will also be byte-padded.
--Ex implementation for ptr, {UInt 16, Word}, [w1,w2]:
--mstore ptr (w1 << 240)
--mstore (ptr+2) w2
--Only when a value is < 1w will you need to save and restore.
--Example for UInt 240, [w]:
--saved <- mask 16 $ mload ptr
--mstore ptr (w << 16 | saved)
assignPtr :: Name -> T -> [Name] -> Seq ()
assignPtr ptr t ws = do
  sz <- numBitsT t
  let bs = (sz `roundedUpMod` 8) `div` 8
      bsFst = let m = bs `mod` 32
              in if m == 0
                 then 32
                 else m
      sh = 8*(32 - bsFst)
  case () of
    _ | bs == 0 -> return ()
      | bs < 32 -> do
          old <- mload ptr
          let [w] = ws
          new <- runEDSLW $ mask sh (EVar old)
            .| (shift sh $ EVar w)
          mstore ptr new
      | let -> do
          let w:ws' = ws
          shifted <- runEDSLW $ shift sh $ EVar w
          mstore ptr shifted
          --This may write beyond the directly addressable range of 16b ptrs
          sequence_ [
            do ptr' <- runEDSLW $ op2 "add" (word off) (EVar ptr)
               mstore ptr' w'
            | (off,w') <- zip (map (+bsFst) $ map (32*) [0..]) ws'
            ]
    
--Implements *ptr#ix* = v
assignPtrFields = error "TODO"

--Scheme: (a,b) -> a; combine a with b starting with the lowest words
--If b is longer than a and a is not a whole number of words, mask the
--highest word of the result.
binaryBitOp :: Name -> String -> Bool -> T -> [Name] -> Seq (T,[Name])
binaryBitOp pfname opcode corruptible t ws_a_b =
  case t of
    Pair a b -> do
      na <- numWordsT a
      nb <- numWordsT b
      if length ws_a_b /= na + nb
        then error $ "Compiler error: something's gone wrong " ++ show
             (pfname,t,na,nb,ws_a_b)
        else do
        let ws_a = take na ws_a_b
            ws_b = drop na ws_a_b
        --Starting from the end of ws_a, combine it with the respective word
        --in ws_b. If |b| < |a|, this may be shorter than the return value.
        ws_combined <- reverse <$> mapM (\(wa,wb) ->
                                           head <$>
                                           runEDSLWord (op2 opcode (EVar wa)
                                           (EVar wb)))
                       (zip (reverse ws_a) (reverse ws_b))
        bitsa <- numBitsT a
        bitsb <- numBitsT b
        case () of
          _ | bitsa == bitsb -> return (a,ws_combined)
            | bitsb < bitsa ->
                return (a, take (na-nb) ws_a ++ ws_combined)
            --a is a whole number of words and thus can't be corrupted
            --(modulo padding, which bit ops corrupt silently)
            --TODO fix that by giving types non-contiguous masks?
            --Sounds like a problem best solved by the programmer
            --1) not applying bitops to structs unless they know what they're
            --doing.
            --2) not fetching structs from arbitrary addresses.
            | bitsa `mod` 256 == 0 ->
              return (a,ws_combined)
            --The first word may be corrupted
            --Note: that's not the case for &, so I pass a flag
            --TODO check the "corrupting" bits aren't just padding.
            | corruptible ->
              let w:ws = ws_combined
                  bitszw = bitsa `mod` 256
              in do
                (w',_) <- runEDSL $ mask bitszw (EVar w)
                return (a,w':ws)
            | otherwise -> return (a,ws_combined)
    _ -> throwE $ BadArgPrimFun pfname t
{-
Mathop rules:
If both are ints, result has max len of both and is signed if either arg is.
Smaller ints must be soft-coerced to the longer type.
If the len of the result is < 256, you must mask it.
-}
maxIntType :: T -> T -> T
maxIntType (Int s1 l1) (Int s2 l2) = Int (if "Signed" `elem` [s1,s2]
                                           then "Signed"
                                           else "Unsigned") (max l1 l2)
pfMathOp :: String -> T -> T -> (Name,Name) -> Seq (T,[Name])
pfMathOp opcode int1@(Int{}) int2@(Int{}) (w1,w2) = do
  let tres = maxIntType int1 int2
  ws1 <- softCoerce tres int1 [w1]
  ws2 <- softCoerce tres int2 [w2]
  (v,_) <- runEDSL $ op2 opcode (EVar $ ws1 !! 0) (EVar $ ws2 !! 0)
  --Mask if len < 256b
  let Int _ len = tres
  w <- if len < 256
       then fst <$> (runEDSL $ mask (fromInteger len) $ EVar v)
       else return v
  return (tres,[v])

truthyE :: E -> Seq Name
truthyE e = do
  (_,ws) <- seqE e
  truthy ws

truthy :: [Name] -> Seq Name
truthy ws = do
  irts <- mapM getIRVarType ws
  --Truthy only works on concrete values
  if all (\case Just (W {}) -> True
                _ -> False) irts
    then do
    v <- newAnonVar
    emitOp [(v,tword)] (Reduce "or") ws
    return v
    else throwE $ BadArgInTruthy ws
--Given the IR vars to assign to a C local, emits the assignment.
--We assume the vars have the correct type.
--x = ws => x#1 : typeof w1 = copy w1 ..
assign :: Name -> [Name] -> Seq ()
assign x [] = return ()
assign x ws = do
  mt <- getIRVarType $ head ws
  case mt of
    Just (W 1 t) -> 
      sequence_ [emitOp [(x ++ "#" ++ show n, W n t)] Copy [w]
                | (n,w) <- zip [1..] ws]
    _ -> throwE $ BadFirstRHSInAssign x mt ws

--target type, source type, words of source value
--Supported coercion: any int -> int, any struct -> struct
{-Struct coercion scheme:
for nth field = name, t in target:
 if source has .name : t', result.name = source.name; break
 if source has nth anon field : t', result.name = source<n>; break
 else result.name = all zeroes --constant sharing could be useful here

Note result.field = source.field also involves soft coercion
-}
softCoerce :: T -> T -> [Name] -> Seq [Name]
--When lengthening to a signed int, signextend
--When shortening any int, mask
--TODO: when it would shorten code sufficiently, replace mask with shl,shr
softCoerce target source ws
  | target == source = return ws
  | Int s1 len1 <- target,
    Int s2 len2 <- source,
    [w] <- ws =
      case () of
        _ | len1 < len2 -> runEDSLWord $ fromInteger len1 `lowestBits` (EVar w)
          | len1 > len2, s1 == "Signed" ->
            runEDSLWord $ signextend (word $ fromIntegral len1) (EVar w)
          | let -> runEDSLWord $ coerce (W 1 target) (EVar w)
  --Adding general tuple coercion
  --Goal: {2,3} can be coerced to {foo: Word, bar: Word}
  --{bar: 1, foo: 1} can be coerced to ditto by swapping field order.
  --For now, no general struct coercion, only tuple -> tuple
  | Just ts1 <- unTupleT target, Just ts2 <- unTupleT source =
    softCoerceTuple ts1 ts2 ws
  | let = throwE $ GenericError $
          "Unsupported in softCoerce " ++ show (target,source,ws)

unTupleT :: T -> Maybe [T]
unTupleT = \case
  Struct padmnmts -> go padmnmts
  _ -> Nothing
  where go = \case
          [] -> Just []
          ((Word,Word),Nothing,t):padmnmts ->
            (t:) <$> go padmnmts
          _ -> Nothing

--Scheme: for each field in target, softCoerce source field and then coerce
--to tuple words.
--I'll add a restriction for now: require the lenghts are equal.
--Is it essential to actually modify the IR type? It's just a safety feature
--to detect bugs in codegen... but it's worth it, I should be able to
--optimize the copies away.
softCoerceTuple :: [T] -> [T] -> [Name] -> Seq [Name]
softCoerceTuple targetTs sourceTs ws
  | length targetTs /= length sourceTs = throwE $ GenericError $
    "Tuple length mismatch: " ++ show (targetTs,sourceTs)
  | otherwise = do
      twss <- splitTuple sourceTs ws
      wss' <- mapM (\(target,(source,ws)) ->
                      softCoerce target source ws) $ zip targetTs twss
      --Now we just assemble the words into a single tuple by copying
      let sourceWs = concat wss'
          resT = tupleT targetTs
      resWs <- mapM (\(i,w) -> do
                        (v,_) <- runEDSL $ coerce (W i resT) (EVar w)
                        return v
                    ) $
               zip [1..] sourceWs
      return resWs
--Given the words of a tuple, divide it into the words of each field and its
--type. Coerces the words so assign works (TODO relax assign? Accurate IR
--types are actually a useful hint when debugging).
--TODO deduplicate if there's any similar logic; use it in primop logic.
splitTuple :: [T] -> [Name] -> Seq [(T,[Name])]
splitTuple [] [] = return []
splitTuple (t:ts) ws = do
  nt <- numWordsT t
  if length ws < nt
    then throwE $ GenericError $ "Too few words in splitTuple: "
         ++ show (t:ts,ws)
     else do
    let wst = take nt ws
    --Now we coerce the words (currently of a tuple IR type) to t[1],t[2]...
    --TODO make/find
    wsFinal <- coerceT t wst
    ((t,wsFinal):) <$> splitTuple ts (drop nt ws)
--The result of coercing 0 to any type t: all zeroes in the bitpattern.
--May not be a valid value of that type; use of e.g. null ptr may be UB.
--We do some free constant sharing here.
nullValue :: T -> Seq [Name]
nullValue t = do
  n <- numWordsT t
  map fst <$> runEDSL (do
    z <- word 0
    sequence [coerce (W i t) (return z) | i <- [1..n]])

--Given a field index, returns the type of the field, bitsize and left offset,
--and the number of padding bits to left and right.
--Note that on the right the padding may include left-padding of the first
--field of the value to the right + the padding of its first field and so on.
--Why number of bits and not just Booleans indicating there are no non-padding
--bits in the same word? Because memory is byte-addressed, and so a
--align byte pad word Byte field that overlaps two words in the stack repr can
--still be read and written cheaply.
--The layout may contain 0-size fields; they don't interrupt contiguous
--padding.
--Note special case for get/put on stack: if the field is leftmost, there's
--guaranteed to only be zero bits to the left of it.
--For memory put/get that's not the case: unless the field is in the last byte
--of the last word, there may be data to write back.
--Note that with the new structLayout implementation 0-sized fields may
--impact layout via alignment.
fieldInfo :: Int -> [Field T] -> Seq (T,Int,Int,Int,Int)
fieldInfo ix fields
  | ix < 0 = throwE $ GenericError $ "Negative ix in fieldInfo: "
    ++ show (ix,fields)
  | otherwise = do
      let len = length fields
      if ix >= len
        then throwE $ GenericError $ "Too great ix in fieldInfo: " ++
             show (ix,fields)
        else return ()
      --Get type, sz, off of each field
      padalszs <- mapM (\((pad,al),_,t) -> do
                          sz <- numBitsT t
                          return (pad,al,sz)) fields
      let (structSz,szoffs) = B.structLayout padalszs
          types = map (\(_,_,t) -> t) fields
          (revPre,(tyField,(szField,offField)),post) =
            preElemPost ix $ zip types szoffs
      --The relevant left-padding is the difference between offset of the
      --first non-0-size field to the left and the end of the field.
      --(Or the sz of the entire struct if there is none)
      --Q: Does the field value's own left-padding matter? No.
      --Bug: the type has a Num instance, so I accidentally filtered out
      --all elems with type <= TyNat 0...)
      let nzRevPre = filter (\(_,(sz,_)) -> sz > 0) revPre
          leftPad = (case nzRevPre of
                      [] -> structSz
                      (_,(_,offLeft)):_ -> offLeft) - (offField + szField)
      --The right-padding is similar, but also includes the right-padding
      --of the first nonzero field to the right. 
      let nzPost = filter (\(_,(sz,_)) -> sz > 0) post
      rightPad <- case nzPost of
                    [] -> return 0
                    (tyRight,(szRight,offRight)):_ -> do
                      lpr <- leftPadding tyRight
                      return $ offField - (offRight + szRight - lpr)
      return (tyField,szField,offField,leftPad,rightPad)
      where
        --Deja vu...
        --Returns reversed prefix, the elem indexed, and the suffix
        --Note we already know n is in range
        preElemPost n = go [] n
        go rpre n (x:xs)
          | n == 0 = (rpre,x,xs)
          | let = go (x:rpre) (n-1) xs

--Given a nested field .field*, return its type,sz,off,leftPad,rightPad
--leftPad and rightPad may include padding from all enclosing structs.
--Left-padding includes the enclosing struct iff sz + off + lp == the sz
--of the struct itself.
--Right-padding is that of the enclosing struct iff off == 0.
fieldsInfo :: [Int] -> T -> Seq (T,Int,Int,Int,Int)
fieldsInfo [] t = throwE $ GenericError $ "fieldsInfo for empty .field*, " ++
                  "struct type = " ++ show t
fieldsInfo [ix] (Struct fields) = fieldInfo ix fields
fieldsInfo (ix:ixs) (Struct fields) = do
  --Fetch enclosed struct
  (tE,szE,offE,lpE,rpE) <- fieldInfo ix fields
  --Ultimate type, its size, offset in the enclosed struct, left and right
  --padding in that struct
  (tF,szF,offF,lpF,rpF) <- fieldsInfo ixs tE
  --If its left-padding reaches all the way to the enclosed struct boundary,
  --left-padding from the enclosing struct is included.
  szEnclosed <- numBitsT tE
  let lpFull = if offF + szF + lpF == szEnclosed
               then lpF + lpE
               else lpF
  --If the field starts at 0, right-padding from the enclosing struct is
  --used. Note that can only occur several times if the right-padding is 0.
  let rpFull = if offF == 0
               then rpE
               else rpF
  --We return the offset in the stack of enclosing structs
  return (tF,szF,offF + offE,lpFull,rpFull)
fieldsInfo ixs t = throwE $ GenericError $
                   "fieldsInfo on non-indexable type: " ++ show (ixs,t)

--Converts .field#n.field2... to #n1#n2#n3... for a given struct type.
--This repeated traversal could perhaps be merged with fieldsInfo, but that
--would make the code more complex.
--Throws an error if 
indicesAndNamesToIndices :: [Either Name Int] -> T -> Seq [Int]
indicesAndNamesToIndices eis t = go eis t
  where go [] _ = return []
        go (ei:eis) t =
          case t of
            Struct fields ->
              case ei of
                Left nm -> do
                  --Look up the index of the name; throwE if not present
                  let nmts = map (\(_,mnm,t) -> (mnm,t)) fields
                      nmtix = filter (\(_,(mnm,t)) -> mnm == Just nm) $
                              zip [0..] nmts
                  case nmtix of
                    (ix,(_,tField)):_ -> (ix:) <$> go eis tField
                    [] -> throwE $ GenericError $
                          "Name not present in struct: " ++ show (nm,fields)
                Right ix
                  | ix >= 0, ix < length fields ->
                    let (_,_,t) = fields !! ix
                    in (ix:) <$> go eis t
                  | let -> throwE $ GenericError $
                           "Index out of bounds in IANTI: " ++ show (ix,fields)
            _ -> throwE $ GenericError $
                 "Attempted to index non-struct type in IANTI: " ++ show (ei,t)

{-
fieldsToSlice :: [Field T] -> [Either Name Int] -> Seq (T,(Int,Int))
fieldsToSlice = go 0
  where go offAccum fields (ix:ixs) = undefined
        name2ix nm fields =
          undefined
-}

{-
--(bit size, left offset) ws => slice of ws
--Starting word from the left: off `div` 256
--Num words: sz rounded up mod 256 div 256
--Right shift: off `mod` 256
--Whether there are bits to the left you need to mask out is Boolean; you need
--only look at whether another field of nonzero size starts before the next
--word boundary.
getSlice :: Bool -> (Int,Int) -> [Name] -> Seq [Name]
getSlice _ (0,_) [] = return []
getSlice bitsToleft (sz,off) ws = do
  let rws = reverse ws
      startIx = off `div` 256
      numWords = (sz `roundedUpMod` 256) `div` 256
      rightShift = off `mod` 256
      --Now we select only the relevant words: those containing the slice
      relWs = take numWords $ drop startIx ws
  --The relevant words must all be right-shifted; if the shift is zero that's
  --a noop
  shiftedWs <- reverse <$> (if rightShift == 0
                            then return ws
                            else mapM (\w -> runEDSL $
                                      word (fromIntegral rightShift) `shr`
                                      EVar w) relWs)
  undefined
-}
--The full padding of a struct field is the field's padding, plus the
--full padding of the leftmost field of its value if it has one.
--Only structs and newtypes may have leftmost field padding; there is no
--support for datatypes right now so only structs.
--Note left-padding is the difference between the type's bitsize and the
--first index from the right which is guaranteed to be zero; a Byte's repr
--on the stack has 248 bits guaranteed to be zero (modulo unsafe coerce),
--but no padding.
leftPadding :: T -> Seq Int
leftPadding = \case
  Struct fields -> do
    padszs <- mapM (\(pad,al,t) -> do
                       sz <- numBitsT t
                       return (pad,al,sz))  $
              map (\((pad,al),_,t) -> (pad,al,t)) fields
    let (szTotal,szoffs) = B.structLayout padszs
    case fields of
      [] -> return 0
      (_,_,t):fields' -> do
        let (szLeft,offLeft):_ = szoffs
        padValue <- leftPadding t
        return $ padValue + szTotal - (offLeft + szLeft)
  _ -> return 0
--Given a struct value (T,[Name]) and (.field | #n)*, get the value.
--This generates code for indexing a struct on the stack.
--Special case, applicable only to get on stack structs: the spare bits
--in the word repr count as padding.
getStructFields :: T -> [Name] -> [Either Name Int] -> Seq (T,[Name])
getStructFields t ws fieldIxs = do
  ixs <- indicesAndNamesToIndices fieldIxs t
  --Return type, its size, offset in the struct, left and right-padding
  --We don't need right-padding, so we ignore it.
  (tRes,szRes,offRes,lpRes,_) <- fieldsInfo ixs t
  if szRes == 0
    --Get on an empty field is a noop
    then return (tRes,[])
    else do
    --If offRes + szRes + lpRes extends all the way to the last bit of the
    --struct, there can be no nonzero bits to the left; we set left-padding
    --to infinity (well, 256 is enough).
    szStruct <- numBitsT t
    let lpFull = if offRes + szRes + lpRes == szStruct
                 then 256
                 else lpRes 
    --How much we must right-shift the field's value when reconstructing it
    let rightShift = offRes `mod` 256
        --The index from the right of the rightmost relevant word
        ixR = offRes `div` 256
        --Ditto for leftmost
        ixL = (offRes + szRes) `div` 256
        --The words containing the field
        relWs = take (ixL-ixR+1) $ drop ixR $ reverse ws
    valueRes <- reconstructField lpFull szRes rightShift relWs
    return (tRes,valueRes)

--Given left-padding, right shift and words in reverse order containing a field
--to be shifted out and glued back together, does so.
--Precondition: ws is nonempty.
--The first word is to be right-shifted by the original amount... if it's
--not the only one, the next index to
--The field size matters, because it determines whether the leftmost word will
--spill over into a new word when right-shifted.
--Field bits of the rightmost word = 256 - rightShift `min` sz
--Of intermediate words: 256
--Of the leftmost: the remainder.
--Complication: the exact value of left-padding matters, because the content
--of the leftmost word may be left-shifted. Ex: there's a byte of left-padding
--and the content is placed in the last byte of the leftmost result word.
--Then you don't need to do any masking!
reconstructField :: Int -> Int -> Int -> [Name] -> Seq [Name]
reconstructField leftPadding sz rightShift ws = do
  unmaskedWs <- reconstructWithoutMasking sz rightShift 0 ws
  --Now we have the value, potentially corrupted with nonzero bits to the left
  --in the leftmost word.
  --Padding starts at bit sz and the first possible corrupt bit at
  --sz+leftPadding.
  --If that's not within the same word, we're good; otherwise we need to mask.
  --{bar:1,foo:2}.bar should not need to mask
  let corruptIx = (sz + leftPadding) `div` 256
      leftmostIx = sz `div` 256
  if corruptIx > leftmostIx
    --We're good
    then return unmaskedWs
    --We need to mask
    else let leftmostSz = sz `mod` 256
         in case unmaskedWs of
              [] -> return [] --hmm... should this ever happen?
              w:ws -> do
                (maskedW,_) <- runEDSL $ mask leftmostSz $ EVar w
                return (maskedW:ws)
--Given size of field, left offset in the relevant words and the words in
--reverse order, returns the field value without any garbage to its left
--masked out.
{-
Algo: copy sz bits from inptr = rsh to outptr = 0
Both source and dest are divided into words: the maximum that can be copied in
one step is min (256 - inptr % 256) (256 - outptr % 256)
while inptr < sz + rsh:
 inix = inptr div 256
 inoff = inptr mod 256
 outix = outptr div 256
 outoff = outptr mod 256
 out[outix] |= in[inix] << (outoff - inoff)
 copied = min (256 - inoff) (256 - outoff)
 inptr += copied
 outptr += copied
-}
--The state can be a map Int -> Expr;
--Nothing |= e => replace with e
--Yay, the logic can be reused for going from field to value!
reconstructWithoutMasking :: Int -> Int -> Int -> [Name] -> Seq [Name]
reconstructWithoutMasking sz rsh outptr ws =
  let ix2e = go rsh outptr M.empty $ map EVar ws
  in map fst <$> (runEDSL $ sequence $ reverse $ M.elems ix2e)
  where go inptr outptr out inws
          | inptr - rsh >= sz = out
          | let = let inix = inptr `div` 256
                      inoff = inptr `mod` 256
                      outix = outptr `div` 256
                      outoff = outptr `mod` 256
                      out' = (outix |= shift (outoff - inoff) (inws !! inix))
                             out
                      copied = min (256-inoff) (256-outoff)
                  in go (inptr+copied) (outptr+copied) out' inws
        (|=) outix e out =
          M.insert outix (case M.lookup outix out of
                            Nothing -> e
                            Just e' -> e .| e') out
--Gets struct<n1><n2>..., also used to implement struct.field
--The result field's offset is the sum of the offsets of <n1><n2>...
--Problem: the true padding to right and left depends on the stack of
--enclosing structs.
--That applies to the left or rightmost nonzero field.
--But you can easily find out if the nested field's padding is contiguous
--with the other padding 
--getStructIndices :: [Field T] -> [Name] -> [Int] -> Seq (T,[Name])
--getStructIndices fs ws indices = error "TODO"

--Generates code for struct.field* = value, where struct is a C local.
-- *ptr.field* = e requires separate treatment; that's what global, *ptr and
-- arr[ix] turns into.
--The argument is a C local rather than a list of IR vars [Name] because
--we're writing to a variable; writing to a value would be nonsensical.
setStructLocal :: Name -> T -> [Either Name Int] -> T -> [Name] -> Seq ()
setStructLocal structCVar structT nmixs valueT valueWs = do
  --error $ "Here: " ++ show (structCVar,structT,nmixs,valueT,valueWs)
  ixs <- indicesAndNamesToIndices nmixs structT
  (fieldT,sz,off,pl,pr) <- fieldsInfo ixs structT
  --Since we're modifying a struct on stack, we can use the spare bits as
  --infinite padding if the field is leftmost
  szStruct <- numBitsT structT
  let fullPL = if off + sz == szStruct
               then 256
               else pl
  let pl = fullPL
  --Needed to compute struct word names from offset:
  nStruct <- numWordsT structT
  --The name of the IR var containing bit offset off
  let structIRVar off = structCVar ++ "#" ++ show (nStruct - (off`div`256))
  --First, soft coerce the value to the appropriate field type
  coercedWs <- softCoerce fieldT valueT valueWs
  if sz == 0
    then return () --writing to empty fields is a noop
    else do
    let leftShift = off `mod` 256
    --"deconstruct" the field value, left-shifting it and splitting
    --it across sz + leftShift div 256 words.
    newFieldWs <- reconstructWithoutMasking sz 0 leftShift coercedWs
    
    or'dFieldWs <- case newFieldWs of
                     --Special case: if there is only one word you may need to
                     --mask to both left and right of the field.
                     --The field starts at leftShift and padding begins at
                     --leftShift + sz; if pl+that > 255 then there's nothing
                     --to the left.
                     --If pr >= leftShift there's nothing to the right.
                     [w] -> do
                       let emptyLeft = leftShift + sz + pl > 255
                           emptyRight = pr >= leftShift
                           oldWord = structIRVar off
                       --error $ "Woo: " ++ show (w,emptyLeft,emptyRight,
                       --                         leftShift,sz,pl)
                       case () of
                         _ | emptyLeft, emptyRight ->
                             return [w]
                           | emptyLeft ->
                             runEDSLWord $ EVar w .|
                             mask leftShift (EVar oldWord)
                           | emptyRight ->
                             --I also min the mask value by the struct size
                             --because otherwise {foo:3,bar:5}.bar = 2
                             --generates a ridiculously large left-mask
                             runEDSLWord $ EVar w .|
                             (shift (sz + leftShift)
                               (maskValue (min szStruct
                                           255 - (leftShift + sz))) &
                                EVar oldWord)
                           --The most complex mask: 0b111..000...111
                           | let ->
                             runEDSLWord $ EVar w .|
                             (op1 "not" (shift leftShift (maskValue sz)) &
                              EVar oldWord)
                     --The first and last words may need to be or'd with old
                     --words with the field masked out.
                     leftmost:ws -> do
                       let intermediate = init ws
                           rightmost = last ws
                           --If the first potential nonzero bit to the left
                           --of the field isn't in the same word, you don't
                           --need to mask the leftmost field word.
                           emptyLeft = (off + sz + pl) `div` 256 /=
                                       (off + sz - 1) `div` 256
                           --Ditto right
                           emptyRight = (off - pr) `div` 256 /=
                                        off `div` 256
                       leftmost' <- if emptyLeft
                                    then return leftmost
                                    else do
                         let leftmostOld = structIRVar (off + sz - 1)
                         fst <$> (runEDSL $
                                   mask ((sz + off) `mod` 256)
                                    (EVar leftmostOld) .|
                                   EVar leftmost)
                       rightmost' <- if emptyRight
                                     then return rightmost
                                     else do
                         let rightmostOld = structIRVar off
                         fst <$> (runEDSL $
                                   mask (off `mod` 256) (EVar rightmostOld) .|
                                   EVar rightmost)
                       return $ [leftmost'] ++
                         intermediate ++
                         [rightmost']
    --Finally, copy the updated words back to the relevant words of the
    --struct var (this has zero runtime overhead).
    let fieldStart = nStruct - (off + sz - 1) `div` 256
    --error $ "Wah: " ++ show (fieldStart,nStruct,off,sz,pl)
    sequence_ [
      emitOp [(structCVar++"#"++show n,W n structT)] Copy [w]
      | (n,w) <- zip [fieldStart..] or'dFieldWs
      ]
  
--The type of the struct is given by the padding, names and types of elements.
--Each word of the struct is the concatenation of slices of fields; the
--cheapest case is when the word contains a single unsliced field.
--Layout: the padded fields are placed rightmost in the struct, with the struct
--itself word-padded.
--New logic using BuildStruct.hs: first get the bitsize of each field, then
--apply its buildStruct function and interpret it.
--Default alignment: bit. TODO add alignment pragmas to struct types and
--exprs.
--Generalization: operate on words instead of Es so it can be used in
--softCoerce etc
buildStruct :: [((Padding,Padding),Maybe Name,T,[Name])] -> Seq (T,[Name])
buildStruct padmnmtws = do
  --Computing the return type:
  let padmnmts = map (\(pad,mnm,t,_) -> (pad,mnm,t)) padmnmtws
      structType = Struct padmnmts
  --First, we compute the layout using structLayout.
  --It needs the padding, alignment and size of each field
  layout <- B.structLayout <$> mapM (\((pad,al),_,t,_) -> do
                                      bsz <- numBitsT t
                                      return (pad,al,bsz)) padmnmtws
  --createStruct needs the layout and the words
  let wss = map (\(_,_,_,ws) -> ws) padmnmtws
  let outputs = B.createStruct layout wss
  ws <- map fst <$> runEDSL (mapM interp outputs)
  return (structType,ws)
  where interp :: B.O [Name] -> Expr
        interp = \case
          B.V ws i -> EVar $ ws !! (i-1)
          B.Shift o sh
            | sh > 0 -> shl (word $ fromIntegral sh) $ interp o
            | sh < 0 -> shr (word $ fromIntegral $ negate sh) $ interp o
            | otherwise -> error $ "Compiler error: 0 shift in BuildStruct"
          o1 B.:|| o2 -> interp o1 .| interp o2
{-
buildStruct padmnmes = do
  padmnmtws <- mapM (\(pad,mnm,e) -> do
                       (t,ws) <- seqE e
                       return (pad,mnm,t,ws)) padmnmes
  let padmnmts = map (\(pad,mnm,t,_) -> (pad,mnm,t)) padmnmtws
      structType = Struct padmnmts
  --For each field value, the words it consists of and the bitsize of the
  --padded field; that's all the information needed to determine the scheme
  --for computing the struct.
  --Note we reverse the words because we assemble the struct from the back!
  bszws <- mapM (\(pad,_,t,ws) -> do
                  bsz <- padWith pad <$> numBitsT t
                  return (bsz,reverse ws)) padmnmtws
  wc <- numWordsT structType
  sws <- buildStructOps structType wc bszws
  return (structType,sws)
-}
--Concat scheme:
--a ++ b = a << bitsizeof b | b
--Starting from the last field, concatenate the last 256b worth of field
--values into an anon var : Word n structType
--Skip 0-sized fields, they have no runtime effect - and should not constrain
--op ordering!
--When you cross a word boundary, you may have partially consumed a field;
--then you should right-shift the remainder.
--The offset of a field depends on previous fields; a word-sized field in
--front of a byte must be divided over two words.
{-Algo:
Compute the left-shift offset of each field word from the end of
the struct. Associate each word with a bitsize (always 256 for word-padded,
at least 1 for bit-padded).
For each word wc-k, include words where off..off+bitsize overlaps with
k*256.. k*256 + 255.
-}
buildStructOps :: T -> Int -> [(Int,[Name])] -> Seq [Name]
buildStructOps st wc bszwss =
  let shiftwss = structLayout bszwss
  in map fst <$> (mapM (buildStructWord st) $ zip [1..wc] shiftwss)
--st (n,[(16,a),(0,b)]) => a << 16 | b : Word n st
buildStructWord st (n,shiftws) = do
  let shifted = map (\case (shift,v)
                             | shift > 0 ->
                               shl (word $ fromIntegral shift) (EVar v)
                             | shift < 0 ->
                               shr (word $ fromIntegral $ negate shift) (EVar v)
                             | let -> EVar v) shiftws
      disjunction = coerce (W n st) $ foldr1 (.|) shifted
  runEDSL disjunction
  
--field values (bitlen, words) -> [struct word recipe]
structLayout :: [(Int,[Name])] -> [[(Int,Name)]]
structLayout bszwss =
  let pwords = prepareBSZWSS bszwss
      pwordoffs = computeOffsets pwords
  in reverse $ map reverse $ divideIntoWords pwordoffs
--I forget what this does but I'm factoring it out of structLayout so I can
--understand the bug I'm hunting
--Reverses the fields and their composite words for computeOffsets.
prepareBSZWSS bszwss =
  splitFields $ reverse $ map (\(bsz,ws) -> (bsz,reverse ws))bszwss
--Given a bitsize and the reversed list of vars of a value, give each a
--bitlen (all but the last is 256).
splitIntoPartialWords :: (Int,[Name]) -> [(Int,Name)]
splitIntoPartialWords (bsz,ws) =
  case ws of
    [w] -> [(bsz,w)]
    w:ws -> (256,w) : splitIntoPartialWords (bsz-256,ws)
--Collect all field words into a list of partial words
splitFields :: [(Int,[Name])] -> [(Int,Name)]
splitFields = (>>= splitIntoPartialWords)
--bitlen, word => offset,bitlen,word
computeOffsets :: [(Int,Name)] -> [(Int,Int,Name)]
computeOffsets = computeOffsets' 0
computeOffsets' off = \case
  [] -> []
  (len,w) : lenws -> (off,len,w) : computeOffsets' (off+len) lenws
--Given a list of partial words, returns the composite words and shift values
--for each struct word (in reverse order)
divideIntoWords :: [(Int,Int,Name)] -> [[(Int,Name)]]
divideIntoWords = diw 0
  where
    --diw 0 generates the first struct word, diw 256 the second etc
    diw _ [] = []
    diw off offlenws =
      let (wordElems,offlenws') = takeBits off offlenws
      in wordElems : diw (off + 256) offlenws'
--Given a starting bit offset, a number of bits to take and a list of partial
--words, takes a prefix of the partial words and includes their shift values
--(may be negative).
takeBits :: Int -> [(Int,Int,Name)] -> ([(Int,Name)],[(Int,Int,Name)])
takeBits = takeBits' []
takeBits' accum off = \case
  --If the word overlaps with the range off..off+255, include it in accum
  --If it extends beyond, don't consume it and stop collecting words
  (o,l,w) : olws
    --The word starts outside the 256b range we're taking
    | o-off > 255 -> (reverse accum,(o,l,w):olws)
    --The word starts inside, but ends outside
    | o-off+l > 256 -> (reverse $ (o-off,w) : accum, (o,l,w) : olws)
    --It starts and ends inside
    | o-off+l >= 0 -> takeBits' ((o-off,w):accum) off olws
  [] -> (reverse accum,[])
  olws -> (reverse accum,olws)

--Since I'm now building complex exprs, a little DSL for that would be useful.
--Example: a << k1 | b << k2 | c : Word n struct
--Derive return types from argument types when running.
--Make it an Ecomp-style monad to enable sharing of internally returned vars.
type EVar = (Name,IRT)
--The creatively named Expression DSL
data EDSL a where
  --Use a var created outside, getting its type
  EVar :: Name -> EDSL EVar
  --Apply an operator to vars, getting one or more return vars
  --TODO change Maybe to Either SeqError?
  App :: Operator -> ([IRT] -> Maybe [IRT]) -> [EDSL EVar] ->  EDSL [EVar]
  (:>>=) :: EDSL a -> (a -> EDSL b) -> EDSL b
  EReturn :: a -> EDSL a
instance Functor EDSL where
  fmap f m = do
    x <- m
    return $ f x
instance Applicative EDSL where
  pure = return
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x
instance Monad EDSL where
  return = EReturn
  (>>=) = (:>>=)
instance MonadFail EDSL where
  fail = error
--Having EDSL operate on (Name,IRT) was probably a mistake... TODO fix.
runEDSLW :: Expr -> Seq Name
runEDSLW e = fst <$> runEDSL e
runEDSLWord :: Expr -> Seq [Name]
runEDSLWord e = runEDSL $ do
  (v,irt) <- e
  return [v]
runEDSL :: EDSL a -> Seq a
runEDSL = \case
  EVar nm -> do
    mt <- M.lookup nm <$> gets irLocalTypes
    case mt of
      Nothing -> throwE $ Couldn'tLookupVarTypeInEDSL nm
      Just t -> return (nm,t)
  App op ty arges -> do
    es <- mapM runEDSL arges
    let argts = map snd es
    case ty argts of
      Nothing -> throwE $ BadArgsInEDSL op es
      Just rets -> do
        --for each ret t in rets, alloc an anonymous var
        retvs <- mapM typedAnonVar rets
        emitOp retvs op (map fst es)
        return retvs
  m :>>= f -> runEDSL m >>= (runEDSL . f)
  EReturn x -> return x
typedAnonVar :: IRT -> Seq EVar
typedAnonVar irt = do
  v <- newAnonVar
  return (v,irt)

type Expr = EDSL EVar
--TODO transition to just using Seq directly...
wword :: Integral n => n -> Seq Name
wword k = runEDSLW $ word k
word :: Integral n => n -> Expr
word k = head <$> App (Push $ Const $ fromIntegral k) (\_ -> Just [tword]) []
tword = W 1 (UInt 256)
--Internal coercion, coerces the given words to the words of the target C type.
--Errors if the number of words given doesn't match the target's word size.
coerceValue :: T -> [Name] -> Seq [Name]
coerceValue t ws = do
  n <- numWordsT t
  if length ws /= n
    then throwE $ GenericError $ "Word size mismatch in coerceValue: " ++
         show (t,n,ws)
    else sequence [runEDSL $ do
                      (v,_) <- coerce (W i t) (EVar w)
                      return v
                  | (i,w) <- zip [1..] ws]
--Coerces an arbitrary var to a var of another type; ignores kind so mem
--can be coerced to word and vice versa!
coerce :: IRT -> Expr -> Expr
coerce irt e = do
  [v] <- App Copy (\[_] -> Just [irt]) [e]
  return v
--Note: the shift value is the first argument, i.e. the top of the stack!
--That's the opposite order of << or >> in C.
shl :: Expr -> Expr -> Expr
shl = op2 "shl"
shr = op2 "shr"
(&) = op2 "and"
(.|) = op2 "or"
--Utility function: shift n shifts an EVar n bits left (or right if n is
--negative)
--If n > 256 or < -256, returns 0
--If n == 0, returns the value unchanged
shift :: Int -> Expr -> Expr
shift n e
  | n > 256 || n < -256 = word 0
  | n > 0 = shl (word $ fromIntegral n) e
  | n == 0 = e
  | n < 0 = shr (word $ fromIntegral $ negate n) e

op1 :: String -> Expr -> Expr
op1 opcode a = do
  [v] <- App (Opcode opcode) (\case [W{}] -> Just [tword]
                                    _ -> Nothing) [a]
  return v
--Useful variant: op2 embedded in Seq
wop2 :: String -> Seq Name -> Seq Name -> Seq Name
wop2 op e1 e2 = do
  w1 <- e1
  w2 <- e2
  runEDSLW $ op2 op (EVar w1) (EVar w2)
op2 :: String -> Expr -> Expr -> Expr
op2 opcode a b = do
  [v] <- App (Opcode opcode) (\case
                                [W {}, W {}] -> Just [tword]
                                _ -> Nothing) [a,b]
  return v
 
--What is the correct arg order...? TODO find out
signextend :: Expr -> Expr -> Expr
signextend = op2 "signextend"

--Using mask rather than shl, shr
--For large fields this will generate a large amount of code; FW: opt for
--program size
--For large masks, not 0 >> k (12 gas, 5 bytes) will be smaller.
--The cost of a byte is 200 gas (not counting future code load costs or
--accounting for execution potentially having a higher gas price due to
--urgency)
--The cost of computing is 9 gas. For an n>5-byte mask, you need to
--execute it (200/9)*(n-5) times before it's worth just pushing it instead
--(modulo the code size limit).
--For n = 32 (the maximum), that translates to exactly 600 - not very much
--in the context of a popular smart contract. I just won't compute masks
--except for the special case of maskValue 255 then.
--FW: take discounted execution intensity into account, make it a configurable
--choice based on intensity and the code size constraint.
--Ex algo: when you run out of code space, try computing the number with the
--highest byte reduction / exec overhead.
--Synonym for lowestBits:
mask :: Int -> Expr -> Expr
mask = lowestBits
wmask :: Int -> Seq Name -> Seq Name
wmask 0 _ = wword 0
wmask 256 e = e
wmask len e = do
  w <- e
  runEDSLW $ maskValue len & EVar w
lowestBits :: Int -> Expr -> Expr
--Opt: if len = 0, just return 0 (but don't discard potential side effects in
--e)
lowestBits 0 e = e >> word 0
lowestBits 256 e = e
lowestBits len e = maskValue len & e
maskValue :: Int -> Expr
maskValue 256 = op1 "not" (word 0) --special case: 30 bytes saved for 3 gas
maskValue len = word $ 2 ^ len - 1
--k + x
addK :: Integral n => n -> Expr -> Expr
addK 0 e = e
addK k e = op2 "add" e (word k)

mulK :: Integral n => n -> Expr -> Expr
mulK k e =
  case k of
    0 -> word 0
    1 -> e
    (-1) -> op2 "sub" (word 0) e
    _ -> op2 "mul" (word k) e
--I have copies all over the place... will not SSAing between SLCs make them
--less efficient?
--Consider (x,f(),x); use fields of tuple.
{-That becomes
a1 = x
a2 = call f(ret) --SLC boundary
ret:
a3 = x
...use a1,a2,a3
Yes, because a1 is live it must be represented at the end of the calling SLC.
But by extending the state to include renamings (thus storing multiple vars
in one word on the stack), I can get around that.
Perhaps I could get phi functions and thus full SSA by making
xN = slot(n) my phi substitute.
while e body =>
outvars = phi(outvars,invars)
It's only applicable if the while breaks.
Phi functions are just noops establishing a dependency.
-}

--Copy an IR var to a new anon var; may become a dup after SSA
--Why a type param? Because the type of the copied word may change, e.g.
--if you create a tuple (w1,w2,w3) in which case copies will be
--Word 1,2,3 of a tuple rather than a uint256.
--Another example: zero-cost coercion, such as uint8 to uint256
copyVar :: IRT -> Name -> Seq Name
copyVar irt nm = do
  mt <- getIRVarType nm
  case mt of
    Nothing -> throwE $ Can'tCopyUnboundIRVar nm
    Just t -> do
      v <- newAnonVar
      emitOp [(v,irt)] Copy [nm]
      return v
--push a static one-word C type
pushK :: T -> StaticValue -> Seq Name
pushK t sv = do
  v <- newAnonVar
  emitOp [(v,W 1 t)] (Push sv) []
  return v

--Used to aid in debugging printed IR modules
comment :: String -> Seq ()
comment = emit . IRComment
emit :: IR -> Seq ()
emit ir = tell [ir]
--If the lhs vars are new, binds them to their type
--If a var v already exists, checks its type matches and errors otherwise
--Repeated vars in the lhs cause an error
--All vars in the rhs must be bound
--Returns the lhs vars
emitOp :: [(Name,IRT)] -> Operator -> [Name] -> Seq [Name]
emitOp nmts op args = do
  typeCheckLHS nmts
  sequence_ [do mt <- getIRVarType arg
                case mt of
                  Nothing -> throwE $ UnboundVarInOpRHS arg nmts op args
                  Just _ -> return ()
            | arg <- args]
  emit $ Op () nmts op args
  return $ map fst nmts
--A fateful decision: no IR var type checking.
--That's to fix x = x + 1 generating an error, because the IR var returned is
--apparently always a tword. That should be fine...
--Kind errors are always nonsensical, so I should maybe add a check for that.
typeCheckLHS :: [(Name,IRT)] -> Seq ()
typeCheckLHS nmts = mapM_ (\(nm,t) -> putIRVarType nm t) nmts
{-
typeCheckLHS = typeCheckLHS' S.empty
typeCheckLHS' :: Set Name -> [(Name,IRT)] -> Seq ()
typeCheckLHS' nms = \case
  [] -> return ()
  (nm,t):nmts ->
    if S.member nm nms
    then throwE $ DuplicateVarsInLHS nm nms
    else do
      mirt <- getIRVarType nm
      case mirt of
        Just t'
          | t' == t -> return ()
          | let -> throwE $ IlltypedLHS nm t t'
        Nothing -> putIRVarType nm t
      typeCheckLHS' (S.insert nm nms) nmts
-}
--Nothing indicates unbound
getIRVarType :: Name -> Seq (Maybe IRT)
getIRVarType nm = M.lookup nm <$> gets irLocalTypes
putIRVarType :: Name -> IRT -> Seq ()
putIRVarType nm t = do
  s <- get
  put s{irLocalTypes = M.insert nm t $ irLocalTypes s}

putCLocalVarType :: Name -> T -> Seq ()
putCLocalVarType x t = do
  s <- get
  let m = cLocalTypes s
  case M.lookup x m of
    Just t' -> error $ "Compiler bug: duplicate putCLocalVarType " ++
      show(x,t,t')
    Nothing -> put s{cLocalTypes = M.insert x t m}

newAnonVar :: Seq Name
newAnonVar = do
  s <- get
  let n = anonVarCounter s
  put s{anonVarCounter = n+1}
  return $ "$anon" ++ show n

--TODO deduplicate...
--(Word) (-1) becomes signextend 0xff, but that's fine: you can just constant
--expand it or replace with 0 - 1.
typeOfInteger :: Integer -> T
typeOfInteger n =
  Int (n <? 0) --it's signed iff it's negative
  (min 256 $ 8 * (max 1 $ byteLen $ abs n))
  --0 is a special case: 1B is more than needed to represent it, but we use
  --that to ensure integers always have a 1-word representation.
  where byteLen 0 = 0
        byteLen n = 1 + byteLen (n `div` 256)
        a <? b = if a < b then "Signed" else "Unsigned"

data NameInfo = IsFunction T
              | IsPrimFun --no type specified because they're overloaded
              | IsLocal T
              | IsUnbound
              --New name types: TyCon and TySyn
              | IsPrimTyCon --no kind info for now
              | IsTySyn --ditto
  deriving (Eq,Ord,Read,Show)
primFunSet :: Set Name
primFunSet = M.keysSet simplePFs

--Given a constructor name, returns its (tag,argT,tycon,fst param,rest)
--Fails if there's no such constructor
getConInfo :: Name -> Seq (Int,T,Name,Name,[Name])
getConInfo nm = do
  cons <- constructors <$> seqrModule <$> ask
  case M.lookup nm cons of
    Nothing -> throwE $ GenericError $
               "No such constructor: " ++ nm
    Just x -> return x

getCNameInfo :: Name -> Seq NameInfo
getCNameInfo nm
  | S.member nm primFunSet = return IsPrimFun
  | let = do
          mod <- askModule
          case M.lookup nm $ defuns mod of
            Just (Defun _ t _ _) -> return $ IsFunction t
            _ -> do
              lts <- gets cLocalTypes
              case M.lookup nm lts of
                Just t -> return $ IsLocal t
                _ -> return IsUnbound

--TODO deduplicate
--This'll become dependent on mod once user-defined types are introduced
numWordsT :: T -> Seq Int
numWordsT t = do
  n <- numBitsT t
  return $ (n `padWith` Word) `div` 256
--Should've written this earlier...
numBytesT :: T -> Seq Int
numBytesT t = do
  n <- numBitsT t
  return $ (n `padWith` Byte) `div` 8
--With alignment, size calc of structs becomes more complex
--TODO deduplicate the logic between size calc, construction and access
numBitsT :: T -> Seq Int
numBitsT = \case
  Int _ n -> return $ fromInteger n
  a :-> b -> return 16
  Ptr r a -> return 16
  Struct padnmts -> do
    padalszs <- mapM (\((pad,al),_,t) -> do
                       sz <- numBitsT t
                       return (pad,al,sz)) padnmts
    let (sz,structure) = B.structLayout padalszs
    return sz
  --Currently the only other use of :$$ is datatypes, which are just wrapped
  --pointers. That will change once I add Proxy a
  _ :$$ _ -> return 16
  t -> error $ "Compiler error: undefd numBitsT for " ++ show t


--I need to type check at the same time...
--integer literals become the smallest type that fits; limit to 256b
--they become signed iff they're negative.
--Var is either a local or a function; disallow placement of primfuns.
--f :$ x is either a function or primfun application
--structs may be multiple words, and is formed via shift and or of its
--underlying words. Tuples can be optimized.
