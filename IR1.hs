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
  anonVarCounter :: Int --makes $anonN
  }
  deriving (Eq,Ord,Read,Show)
--So I can add info about the function being compiled, specifically the return
--type but maybe more stuff in future (opt choices?).
data SeqR = SR {
  seqrModule :: Module,
  seqrFunction :: D
               }
  deriving (Eq,Ord,Read,Show)
--Top-level function: given a module, generates the IR for each function.
--Pruning based on actual calls made from main can be done later.
--FW problem: the IR output may need additional info for placement, such as
--whether the code is a library, exported functions and JTs
data IRModule = IRM {
  irDefuns :: Map Name (Arity,[IR])
  }
  deriving (Eq,Ord,Read,Show)
--The number of argument words a function takes beyond $ret; needed for asm
--generation.
type Arity = Int
seqModule :: Module -> Either SeqError IRModule
seqModule mod = do
  --First, handle tysyns. After this phase they're irrelevant to output,
  --having been substituted away. However, they should still be in the
  --interface info.
  mod' <- handleTySyns mod
  let mod = mod'
  let fdefs = M.toList $ defuns mod
  irdefs <- mapM (\(fnm,defun) ->
                    let seqr = SR {seqrModule = mod,
                                   seqrFunction = defun
                                  }
                        seqs = SS {irLocalTypes = M.empty,
                                   cLocalTypes = M.empty,
                                   anonVarCounter = 0
                                  }
                    in case runSeq (seqDefun defun) seqr seqs of
                         (Left serr, _, _) -> Left serr
                         (Right arity, irs, _seqs) -> return (fnm,(arity,irs))
                 )
            fdefs
  return $ IRM {irDefuns = M.fromList irdefs}

--First checks for cycles in the type synonyms.
--Substitute all types and check their kinds. It's disappointing that can't
--be done in the Seq monad...
--The desugaring phase has already ruled out tysyns clashing with other defs.
--While the kind check is deferred until use rather than done in the check of
--the type decl itself, I can check whether the tysyn RHS contains type
--constructors that aren't in scope.
--For now, that only includes the primitive tycons.
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
  --TODO add coerce and substitute in the function body
  return mod{tysyns = tysyns', defuns = defuns'}

--What can go wrong? An underapplied syn or a kind check failure.
--In future the kind check will need to consider user-defined types.
--Without a kind check on data decl creation, you need to defer the check until
--data types are fully applied and then see whether their constructor args are
--Type (or in future, a non-stack value type).
--For now I'll just do the substitution.
substDefuns :: Syns -> Module -> Either SeqError (Map Name D)
substDefuns syns mod = do
  let defs = map snd $ M.toList $ defuns mod
  sdefs <- mapM (\case Defun fnm t pat body -> do
                         t' <- substDefunT t
                         return $ (fnm,Defun fnm t' pat body)) defs
  return $ M.fromList sdefs
  where substDefunT t =
          case applyTySyns syns t of
            Left (Left (nm,ts)) -> Left $ UnderAppliedSynInDefun nm ts
            Left (Right (pnts,ts)) -> Left $ ArgsAppliedToStructInDefun pnts ts
            Right t' -> Right t'

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
    PDot p field -> error "TODO field pattern matching"
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
isolate :: Seq a -> Seq (a,[IR])
isolate m = do
  s <- get
  (a,irs) <- censor (const []) $ listen m
  s' <- get
  put s{anonVarCounter = anonVarCounter s'}
  return (a,irs)

seqE :: E -> Seq (T,[Name])
seqE = \case
  --integer literals may be at most one word
  EInteger n -> do
    let t = typeOfInteger n
    v <- pushK t (Const n)
    return (t,[v])
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
  EStruct padnmes -> buildStruct padnmes
  --In future, I may add new uses of .field beyond struct, such as
  --n.slice(a,b)
  --Structs with duplicate field names should arguably be forbidden, but I
  --don't need to check for them here; do so in kind check (TODO) and
  --on struct creation.
  e :. field -> do
    (t,ws) <- seqE e
    case t of
      Struct fields -> do
        let kvs = do
              (_,mnm,t) <- fields
              case mnm of
                Just nm -> [(nm,t)]
                _ -> []
        case lookup field kvs of
          Just t -> do
            --Now we need to consider padding; I'll put the logic for field
            --access in StructBuilder
            error "TODO .field"
          Nothing -> throwE $ GenericError $
          ".field of nonexistent field in struct: " ++ show (e,t,field)
      _ -> throwE $ GenericError $ ".field of non-struct type: " ++
        show (e,t,field)

--The compilation schemes for simple primfuns (where their argument is evaluated
--normally rather than short-circuited).
--Badargs should lead to a Seq exception.
simplePFs :: Map Name (T -> [Name] -> Seq (T,[Name]))
simplePFs = M.fromList [
  --Mathops
  --C has unary +, but it's pretty vestigial... I'll just ignore it
  ("+",\t ws ->
      case (t,ws) of
        (Pair t1@(Int s1 len1) t2@(Int s2 len2),[w1,w2]) ->
          pfMathOp "add" t1 t2 (w1,w2)
        _ -> throwE $ BadArgPrimFun "+" t),
  --Recall: mul/smul, div/sdiv need special treatment
  --Binary bitwise ops
  ("&", binaryBitOp "&" "and" False),
  ("|", binaryBitOp "|" "or" True),
  ("^", binaryBitOp "^" "xor" True)
                       ]
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
 if source has nth field = __fieldN : t', result.name = source.__fieldN; break
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
  --For now, no general struct coercion, only tuple -> tuple
  | Just ts1 <- unTupleT target, Just ts2 <- unTupleT source =
    softCoerceTuple ts1 ts2 ws

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
          
{-
--TODO update pkgs...
(!?) :: [a] -> Int -> Maybe a
[] !?  _ = Nothing
(x:xs) !? n
  | n == 0 = Just x
  | let = xs !? n
-}
                             
--The type of the struct is given by the padding, names and types of elements.
--Each word of the struct is the concatenation of slices of fields; the
--cheapest case is when the word contains a single unsliced field.
--Layout: the padded fields are placed rightmost in the struct, with the struct
--itself word-padded.
--New logic using BuildStruct.hs: first get the bitsize of each field, then
--apply its buildStruct function and interpret it.
--Default alignment: bit. TODO add alignment pragmas to struct types and
--exprs.
buildStruct :: [((Padding,Padding),Maybe Name,E)] -> Seq (T,[Name])
buildStruct padmnmes = do
  --First we get the types and words
  padmnmtws <- mapM (\(pad,mnm,e) -> do
                       (t,ws) <- seqE e
                       return (pad,mnm,t,ws)) padmnmes
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
word :: Integer -> Expr
word k = head <$> App (Push $ Const k) (\_ -> Just [tword]) []
tword = W 1 (UInt 256)
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
op1 :: String -> Expr -> Expr
op1 opcode a = do
  [v] <- App (Opcode opcode) (\case [W{}] -> Just [tword]
                                    _ -> Nothing) [a]
  return v
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
--Synonym:
mask :: Int -> Expr -> Expr
mask = lowestBits
lowestBits :: Int -> Expr -> Expr
lowestBits len e = (word $ 2 ^ len - 1) & e
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
  (min 256 $ 8 * (byteLen $ abs n))
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
primFunSet = M.keysSet simplePFs {-S.fromList $ concat $ map words [
  --Ptr primops
  "deref",
  --Mathops
  "+ * - / negate %",
  --Logops (with short-circuiting)
  "&& || !",
  --Bitops
  "& | ~ ^"
  --TODO: EVM ops
  ]-}

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
--With alignment, size calc of structs becomes more complex
--TODO deduplicate the logic between size calc, construction and access
numBitsT :: T -> Seq Int
numBitsT = \case
  Int _ n -> return $ fromInteger n
  a :-> b -> return 16
  Struct padnmts -> do
    padalszs <- mapM (\((pad,al),_,t) -> do
                       sz <- numBitsT t
                       return (pad,al,sz)) padnmts
    let (sz,structure) = B.structLayout padalszs
    return sz
  t -> error $ "Compiler error: undefd numBitsT for " ++ show t


--I need to type check at the same time...
--integer literals become the smallest type that fits; limit to 256b
--they become signed iff they're negative.
--Var is either a local or a function; disallow placement of primfuns.
--f :$ x is either a function or primfun application
--structs may be multiple words, and is formed via shift and or of its
--underlying words. Tuples can be optimized.
