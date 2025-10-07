{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Structured.Convert where

import AST.DTs hiding (Var,Unit,Pair)
{-(Pat(),E(),S(),T(..),Name(),Module(..), pattern UInt,
                pattern (:->), pattern Array)-}
import AST.Util (rollTyApps,unrollTyApps,region2T)
import qualified AST.DTs as A
import Structured.DTs --(Stmt(),Structured())
import qualified Structured.DTs as IR
import Mono.Mono (MonoS(..),instT)
import Const.Serialize
import Core.RestrictedCore
import Util (complainIf)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad (forM,forM_)
import Data.List (elemIndex)

--Converts each C function to the structured IR, breaking up subexprs into a
--flat sequence of assignments and making stack explicit.
--The const values for each global initializer and datatype tag have also been
--computed, enabling case => ifte opts.
--Algo:
--for each (f,(t,(p,s))) in exploredFuns, convert its s to structured Stmts
convert :: (Module,MonoS,Map (Name,[T]) Integer, SerS) ->
           Either ConvertError Structured
convert (mod,monoS,sizes,serS) = do
  --Structured compilation doesn't use sizeof
  (defs,_) <- runExcept $
              flip runStateT initConvertS $
              flip runReaderT (mod,monoS,serS) $
              M.fromList <$> (forM (M.toList $ exploredFuns monoS)
                              (\((f,params),(a :-> b,(p,s))) -> do
                                  (pat,stmts) <- convertF b p s
                                  return (FPoly f params $ fun2coreT a b,
                                          (pat,stmts))))
  let gs = M.fromSet (\g ->
                        let Just (r,_me) = M.lookup g $ globals mod
                            Just ([],t) = M.lookup g $ tysigs mod
                        in Ptr (region2T r) t) $ exploredGlobals monoS
      --globals mod [g] = (r,Just e) => stats[g] = e
      stats = M.fromList $ do
        g <- S.toList $ exploredGlobals monoS
        let Just (_r,me) = M.lookup g $ globals mod
        case me of
          Nothing -> []
          Just e -> return (g, MkConst e)
  return Structured{sdefuns = defs,
                    sglobals = gs,
                    sstatic = stats,
                    stagSchemes = sersTagSchemes serS,
                    sdtsInfo = dtsInfo mod,
                    ssizeof = sizes
                   }
--Read: Module, MonoS, sizeof info, SerS
type ConvertR = (Module,MonoS, SerS)
--State: scope + stmts (it's just convenient to have in State)
--Also need to alloc new vars
data ConvertS = CS {
  csAllocCtr :: Int,
  csScope :: [Var], --the stack vars, hd = top of stack
  --Loop scopes isn't necessary (the declared scope is the scope before
  --the break/continue rather than the scope it jumps to), but we need to
  --know whether we are in a loop.
  csInALoop :: Bool,
  --csLoopScopes :: [[Var]], --for declaring scope before a break/continue
  csOutput :: [Stmt]
  }
  deriving (Eq,Ord,Read,Show)
initConvertS = CS {
  csAllocCtr = 1,
  csScope = [],
  csInALoop = False,
  csOutput = []
  }
data ConvertError = GenericCE String --placeholder
                  | PlusPluslikeOnWildlikePattern Name Bool Pat
                  | OPAssignOnWildlike E Pat
                  | BreakOutsideLoop
                  | ContinueOutsideLoop
                  --Case errors
                  | DefaultNotLast (Pat,S)
                  | DuplicateConsInRefutableCases [Name]
                  | DefaultCaseDespiteFullCoverage [Name]
                  --Fun LHS errors
                  | ArgPatHasDuplicateVars Pat
                  | NonTupleyFunLHS Pat
  deriving (Eq,Ord,Read,Show)
--I don't annot poly names (fs and Cons) with actual type, nor do I do so for
--(:$), so I must reconstruct them from params... a complexity and perf drag.
type Convert = ReaderT ConvertR (StateT ConvertS (Except ConvertError))

--TODO make a class for this, I have a ton of them...
--TODO document anon var naming conventions to prevent clashes
cNewVar :: T -> Convert Var
cNewVar t = do
  s <- get
  let n = csAllocCtr s
  put s{csAllocCtr = n+1}
  return $ Mono ("$v" ++ show n) t

--Calling convention: ((arg,$ret),env) -> End#
--I don't disallow non-tuple lhses in Mono... but I should here.
--Change Core Lambda to have a single var as its lhs, then bind using id#?
--Then id must be able to operate on state types.
--If I pass a single var, I must recognize when one of its arguments is
--unused semantically.
--For now I'll use a Pattern as the lhs and set scope to flattern the vars
--first thing.
--Need to enforce no duplicate vars when converting Pat to Pattern
--Need rett to type $ret :: (rett,Env) -># End#
--Oh no, I forgot to convert called functions to Core funs (where Env is
--explicit) before calling them! Actually that's fine: the Core implem of the
--Call pseudo-op just needs to convert it.
convertF :: T -> Pat -> S -> Convert (Pattern,[Stmt])
convertF rett p s = do
  (vs,val) <- pat2Pattern p
  let ct = contT rett
      --Changed to (a * $ret * stk, env)
      pat = P $ tupleV [foldr1 Pair [val,
                                     Var $ Mono "$ret" ct,
                                     Var $ Mono "$stk" $ TyVar "stk"],
                        envV]
  stmts <- snd <$> collect (setScope vs >> convertS s)
  return (pat,stmts)

--Returns a value so I can easily combine it with envV
--Also returns the non-wild vars so they (and only they) can be put in scope
--Valid arg patterns p ::= () | _ | x | Pair p p
--Wild becomes a new var which is discarded.
pat2Pattern :: Pat -> Convert ([Var],Value)
pat2Pattern p = do
  (vs,val) <- go p
  complainIf (S.size (S.fromList vs) < length vs)
    $ ArgPatHasDuplicateVars p
  return (vs,val)
    where
      go = \case
        PWild (Just t) -> do
          v <- cNewVar t
          return ([], Var v)
        TypedPVar (Just t) v ->
          let var = Mono v t
          in return ([var], Var var)
        PCon "Unit" _ _ -> return ([],Unit)
        --The pair fields may be out of order or missing...
        --No need to normalize (_,_) to _, it has no runtime impact anyway?
        PCon "Pair" (Just [a,b]) fields -> do
          (vs1,val1) <- lookupField a "fst" fields
          (vs2,val2) <- lookupField b "snd" fields
          return (vs1 ++ vs2, Pair val1 val2)
        --TODO find a better adjective than "tupley"...
        p -> throwError $ NonTupleyFunLHS p
      lookupField t field fields =
        case lookup field fields of
          Nothing -> go $ PWild (Just t)
          Just p -> go p
          
--Only A.Declare modifies the scope.
--I must get the type of each expression, but I don't cache it; if I did so
--at every node or annotated names in E with type this would be simpler.
convertS :: S -> Convert ()
--The only case that modifies the scope:
--Note that unshadowing should guarantee the nm is not in scope already.
convertS (A.Declare nmes) =
  forM_ nmes (\(nm,e) -> do
                 scope <- getScope
                 v <- convertE e
                 let t = typeOfVar v
                     local = Mono nm t
                 emitStmt $ Var local IR.:= OpE (Op "id#" [t], Var v)
                 setScope $ local:scope)
convertS s = cleanup (go s)
  where
    go :: S -> Convert ()
    go = \case
      --Evaluates e; cleanup pops the result
      SE e -> convertE e >> return ()
      --Tail call recognition is better done at the Core level, where it
      --can synergize with other opts.
      A.Return e -> do
        v <- convertE e
        emitStmt $ IR.Return v
      --Initial scope: S
      --Eval truthy# e, branch on it.
      --The cases have scope S => S.
      A.Ifte e th el -> do
        scope <- getScope
        v <- convertE e
        let Mono _ t = v
        w <- emitOp (Op "truthy#" [t]) (Var v) (UInt 32)
        setScope scope
        ths <- snd <$> collect (convertS th)
        setScope scope
        els <- snd <$> collect (convertS el)
        emitStmt $ IR.Ifte v ths els
      --First collect the code for eval of e into its own [Stmt];
      --branch on the v returned.
      --The s has scope S => S.
      A.While e body -> do
        scope <- getScope
        (v,estmts) <- collect $ convertE e
        setScope scope
        (_,bstmts) <- collect $ inLoop $ convertS body
        emitStmt $ IR.While estmts v bstmts
      --Special case: case e of p -> s => SE (p=e);{s}?
      --Not quite: the e is evaluated before the subexprs in p!
      A.Case e [(p,s)] -> do
        v <- convertE e
        mp' <- evalPatternEs p
        case mp' of
          Nothing -> return ()
          Just p' -> assign p' v
        convertS $ Block [s]
      --case patterns form: (RefutableBoxed* | RefutableUnboxed*)[Default]
      --The def of BCon, UBCon and default are given in classifyCasePat
      A.Case e pat_ss -> handleCase e pat_ss
      --Collect the generated stmts, then reset the scope.
      --In fact, cleanup does that for free...
      Block ss -> mapM_ convertS ss
      --TODO check we're in a loop.
      A.Break -> do
        b <- gets csInALoop
        if not b
          then throwError BreakOutsideLoop
          else emitStmt IR.Break
      A.Continue -> do
        b <- gets csInALoop
        if not b
          then throwError ContinueOutsideLoop
          else emitStmt IR.Continue
    --Resets the scope
    cleanup :: Convert () -> Convert ()
    cleanup c = do
      scope <- getScope
      c
      setScope scope

--Compiles a case statement with >1 cases
--If there's a refutable case for every constructor then there should be no
--default.
handleCase :: E -> [(Pat,S)] -> Convert ()
handleCase e pat_ss = do
  --First: [(Pat,S)] -> (boxity, refutable cases, Maybe default)
  (boxity, refutable, md) <- handleCase1 $ pat_ss
  --Next: fail if two refutable cases have the same top-level con.
  do let cons = map (\(PCon con _ _, _) -> con) refutable
     --TODO use complainIf
     if S.size (S.fromList cons) < length cons
       then throwError $ DuplicateConsInRefutableCases cons
       else return ()
     --Fail if there's a default despite the refutable cases offering full
     --coverage.
     b <- casesOfferFullCoverage cons
     complainIf (b && md /= Nothing) $ DefaultCaseDespiteFullCoverage cons
  --Evaluate e
  scope <- getScope
  v <- convertE e
  let t = typeOfVar v
      (TyCon tycon,ts) = rollTyApps t
  tagScheme <- do
    --The tag is not an ordinary field, so typeOfDotE won't work...
    --Fortunately the monomorphized tag type is available in monoS.
    (_,monoS,_) <- ask
    let Just tagScheme = M.lookup (tycon,ts) $ exploredDTs monoS
    return tagScheme
  let tagT = case tagScheme of
               N16 -> UInt 1
               N1 len -> UInt $ fromIntegral len
               Custom t _ -> t
  --Whether to branch on inline or boxed tag depends on boxity
  tag <- if boxity
         then do
    --(v.unImplTyCon)->tagImplTyCon
    let ptrField = "unImpl"++tycon
    ptrt <- typeOfDotE ptrField ts
    let Ptr r implDT = ptrt
    v' <- emitOp (GetField [NamedField ("unImpl"++tycon) ts]) (Var v) ptrt
    --Another coerce with no runtime impact
    v'' <- emitOp (GetFieldPtr [NamedField ("tagImpl"++tycon) ts]) (Var v')
           (Ptr r tagT)
    --We call the deref function here (it should be inlined later)
    deref v''
         else do
    emitOp (GetField [NamedField ("tag"++tycon) ts]) (Var v) tagT
  --The set of possible consts, determined by the tag scheme + cons:
  constSet <- getConstSet (tycon,ts)
  --Compute the (const,stmts) list and default
  const_stmtss <- mapM (refutableCase scope v) refutable
  dflt <- case md of
            Nothing -> snd <$> collect
              (do setScope (v:scope)
                  callCFun "revertValue" [TyCon"Unit"] Unit)
            Just (p,s) -> snd <$> collect
              (do setScope (v:scope)
                  mep <- evalPatternEs p
                  case mep of
                    Nothing -> return ()
                    Just ep -> assign ep v
                  setScope scope
                  convertS s)
  --The scope before the caseTag:
  setScope $ tag:v:scope
  --The same function can be used for matching against a single pattern in
  --either case; the EvaluatedPat knows whether it's boxed or not.
  emitStmt $ CaseTag v constSet const_stmtss dflt

--Checks whether the refutable cases include every relevant constructor.
--Ex: Nil, Cons and False, True would qualify.
--It assumes that the con list contains no duplicates and that it is nonempty
--(which has already been checked).
casesOfferFullCoverage :: [Name] -> Convert Bool
casesOfferFullCoverage cons = do
  (_relcon,reltycon) <- getRelCon $ head cons
  mod <- cGetModule
  let Just dti = M.lookup reltycon $ datatypes $ dtsInfo mod
  return $ length cons == length (dtCanonicalCons dti)

--v is the value which will be matched against the pats. The tag check of the
--top-level con is omitted.
--Why return a list and not a map? Because earlier cases dominate later ones;
--later cases with a tag bit-equal to an earlier one are never executed.
--However, we can't in general determine const equality at this stage.
refutableCase :: [Var] -> Var -> (Pat,S) -> Convert (Const,[Stmt])
refutableCase scope v (p@(PCon con (Just params) _),s) = do
  const <- getConTag con params
  (_,stmts) <- collect $ do
    --Scope at start of case, before matching
    setScope (v:scope)
    --Evaluate subexprs in the pattern
    mep <- evalPatternEs p
    --It's refutable, so guaranteed not to be trivial
    let Just ep = mep
    assign (elideTagCheck ep) v
    --Scope at start of body
    setScope scope
    convertS s
  return (const,stmts)
--Get the set of possible tags of a case-inspectable type (which currently
--means types with constructors, but may include integers in future).
--monoS doesn't contain enough info to reconstruct the tag set (you also need
--the number of constructors for N1 and N16), but serS does.
--Precondition: only called on monots with non-nil tag scheme
getConstSet :: (Name,[T]) -> Convert ConstSet
getConstSet con_ts = do
  (_,_,serS) <- ask
  let Just (cons,tagScheme) = M.lookup con_ts $ sersTagSchemes serS
      numcons = fromIntegral $ length cons
  case tagScheme of
    Nil -> error "Compiler error: this should never happen."
    N1 len -> return CSN1 {csSz = len,
                           csLo = 0,
                           csHi = numcons - 1
                          }
    N16 -> return CSN16 {csLo = 0,
                         csHi = 16 * (numcons - 1)
                        }
    Custom _t con2e_ser ->
     return $ ConstSet $ S.fromList $ map (MkConst . fst) $ M.elems con2e_ser
--Given a constructor which may be boxed, get its "relevant" con and tycon.
--For an unboxed con, that's the con and its tycon;
--for a boxed con that's ImplCon and ImplTyCon.
getRelCon :: Name -> Convert (Name,Name)
getRelCon con = do
  mod <- cGetModule
  let Just ci = M.lookup con $ conInfo $ dtsInfo mod
      tycon = conParent ci
      --rel as in relevant
      (relcon,reltycon) = if conBoxed ci
                          then ("Impl"++con,"Impl"++tycon)
                          else (con,tycon)
  return (relcon,reltycon)
--Get the tag of a given monomorphic constructor
getConTag :: Name -> [T] -> Convert Const
getConTag con params = do
  (mod,_,serS) <- ask
  --First get tycon from con using mod
  (relcon,reltycon) <- getRelCon con
  --Then get tag scheme from serS; todo deduplicate tag computation logic
  let Just (cons,tagScheme) = M.lookup (reltycon,params) $ sersTagSchemes serS
  case tagScheme of
    Nil -> error "Compiler error: !?"
    Custom t con2e_ser ->
      let Just (e,ser) = M.lookup relcon con2e_ser
      in return $ MkConst e
    _ | Just ix <- elemIndex relcon cons ->
          return $
          MkConst $
          case tagScheme of
            N1 len -> TyApp "fromWord" [TyCon "Unsigned",
                                        fromIntegral len] :$
                      EInteger (fromIntegral ix)
            N16 -> TyApp "fromWord" [TyCon "Unsigned", 1] :$
                   EInteger (fromIntegral $ ix*16)
--Generates a function call to the function deref defined in Prim; it must be
--inlined later for the compiler to be remotely efficient.
--The work of dispatching based on region and sizeof is done later.
deref :: Var -> Convert Var
deref ptr = do
  let t = typeOfVar ptr
  case t of
    Ptr r a -> do
      let ft = Ptr r a :-> a
      f <- emitOp (Const ft $ MkConst $ TyApp "deref" [r,a]) (Var ptr) ft
      call f (Var ptr)
    _ -> error "Compiler error: deref called on non-pointer!"
  
--Because the cases are well-typed, there will never be a mix of retutable
--boxed and unboxed. The only possible error is a default case that isn't last.
--On the optimistic path (where the program compiles) all cases must be
--inspected, so I do so right away.
--Possible opt: the DT can be retrieved once instead of once per classify.
handleCase1 :: [(Pat,S)] -> Convert (Bool, [(Pat,S)], Maybe (Pat,S))
handleCase1 pat_ss = do
  cpt_pat_ss <- forM pat_ss (\(pat,s) -> do
                                cpt <- classifyCasePat pat
                                return (cpt,(pat,s)))
  let refutable = init cpt_pat_ss
  forM_ refutable (\case (Default,ps) -> throwError $ DefaultNotLast ps
                         _ -> return ())
  let boxity = let (cpt,_) = head refutable
               in cpt == RefutableBoxed
      (cpt,ps) = last cpt_pat_ss
  return $ if cpt == Default
           then (boxity, init pat_ss, Just ps)
           else (boxity, pat_ss, Nothing)

--1) Boxed con, ImplDT has >1 con
--2) Unboxed con, DT has >1 con
--3) Any other pattern
--Note the pattern (True,False) is refutable in the strict sense, but here
--I am concerned only with whether the top-level con is refutable.
data CasePatType = RefutableBoxed
                 | RefutableUnboxed
                 | Default
  deriving (Eq,Ord,Read,Show)
classifyCasePat :: Pat -> Convert CasePatType
classifyCasePat = \case
  PCon con _ _ -> do
    mod <- cGetModule
    let Just ci = M.lookup con $ conInfo $ dtsInfo mod
        tycon = conParent ci
        reltycon = if conBoxed ci then "Impl"++tycon else tycon
        Just dti = M.lookup reltycon $ datatypes $ dtsInfo mod
        gt1 = length (dtCanonicalCons dti) > 1
    return $ if gt1
             then if conBoxed ci
                  then RefutableBoxed
                  else RefutableUnboxed
             else Default
  _ -> return Default

--Sets the csInALoop flag for the duration of the action
inLoop :: Convert a -> Convert a
inLoop c = do
  s <- get
  put s{csInALoop = True}
  a <- c
  modify (\s' -> s'{csInALoop = csInALoop s})
  return a

--Each expr returns a single var; it may be split with a copy
--Constant expressions could become a Const bound to a new var.
--Important: that includes functions and global pointers.
--For now, turn leaf consts into const primops; CE later. Indeed, doing so
--by symbolic eval is more general than identifying syntactic consts.
--Static calls can later be detected by symbolic eval.
--Since locals have been unshadowed, they can be translated straightforwardly
--to function params. Emit no code and simply return the var.
--Note the Var contains type info, so no need to return a separate T.
--Invariant: every expr of type t pushes a generated var of type t; any
--subexprs are consumed. I use cleanup for that.
convertE :: E -> Convert Var
convertE = go
  where go = cleanup go'
        go' = \case
          --w: Emit op newvar = Const Word n
          EInteger n ->
            emitOp (Const (UInt 32) $ MkConst (EInteger n)) Unit (UInt 32)
          --A local: dup and return corresponding var
          --Why dup? Because I expect a given stack effect...
          TypedVar (Just t) nm ->
            emitOp (Op "id#" [t]) (Var (Mono nm t)) t
          --Short-circuiting ops; a && b desugars to scAnd (a,b),
          --a || b to scOr (a,b)
          --Short-circuiting is only applied when the argument is an explicit
          --pair; it is also applied to scAnd/Or (a,b) because it's
          --indistinguishable from a &&/|| b post-desugaring.
          --Function application: recursively eval f and x, then
          --emit a call (not a primop!)
          f :$ x -> do
            vf <- go f
            vx <- go x
            tf <- cTypeOf f
            let _a :-> b = tf 
            call vf $ Var vx
          --case permits one-level fallible patterns, e.g. Cons True xs
          --The subpatterns True and xs are matched the same way as assignment:
          --If the con doesn't match (as in True = False), revertValue ().
          --Note p may contain subexprs in *e or p!e which must be evaluated
          --before e and bound to anonymous vars.
          p A.:= e -> do
            mp' <- evalPatternEs p
            ve <- go e
            case mp' of
              Nothing -> return ()
              Just p' -> assign p' ve
            return ve
          EArray (Just t) es ->
            mapM go es >>= primMkArray t
          --This is either an explored fun or explored global
          TyApp nm params -> do
            (mod,monoS,_) <- ask
            t <- case M.lookup (nm,params) $ exploredFuns monoS of
                   Just (t,_) -> return t
                   _ -> if M.member nm $ globals mod
                        then let Just (_,t) = M.lookup nm $ tysigs mod
                             in return t
                        else error $ "Compiler error: TyApp" ++
                             show (nm,params)
                             ++ "is neither function nor global"
            emitOp (Const t $ MkConst $ TyApp nm params) Unit t
          --Ex: p += k
          --That becomes p' <- eval subexprs in p
          --p' = (interpret as E(p') + k)
          OPAssign (Just opf) p _ e -> do
            --First eval exprs to prevent duplicated side effects
            p' <- do mp' <- evalPatternEs p
                     case mp' of
                       Nothing -> throwError $ OPAssignOnWildlike opf p
                       Just p' -> return p'
            old <- evaluatedPat2Value p'
            operand <- go e
            --cTypeOf just looks at the f to determine the type of f :$ x,
            --so this works:
            t <- cTypeOf (opf :$ EInteger 0)
            vf <- go opf --A const, so when it's evaluated is irrelevant
            --Note all ops in op assignment are of type (a,a) -> a
            new <- call vf $ Pair (Var old) $ Pair (Var operand) Unit
            assign p' new
            return new
          -- ++x; means {var y = x; x = inc x; y}
          --TODO ensure ++_ et al mention inc in mono!
          --TODO annotate PPPre et al with type, dedup with OPAssign
          PPPre p -> plusplus "inc" True p
          PPPost p -> plusplus "inc" False p
          MMPre p -> plusplus "dec" True p
          MMPost p -> plusplus "dec" False p
          --Eval the given fields in textual order; set the missing ones to
          --null#. Note I then need to support a null# Core primitive!
          --That requires I know the types of each field, which is fortunately
          --easy.
          ConRecord con (Just params) field_es -> do
            --Eval the given fields in textual order
            field2v <- M.fromList <$>
                       forM field_es (\(field,e) -> (,) field <$> go e)
            mod <- cGetModule
            let dtsi = dtsInfo mod
                Just ci = M.lookup con $ conInfo dtsi
                field_ts = conFields ci
                tycon = conParent ci
            --For each field in the constructor, use the given value
            --or null#@[t]() if it's missing.
            vs <- forM field_ts (\(field,t) ->
                                   case M.lookup field field2v of
                                     Nothing -> emitOp (Op "null#" [t]) Unit t
                                     Just v -> return v)
            --Con vs :: TyCon  params
            emitOp (MkCon con params) (vars2value vs) $
              unrollTyApps (TyCon tycon) params
          --Optimize (local | *p) .field* at the Core level.
          Dot e (Just params) field -> do
            v <- go e
            t <- typeOfDotE field params
            emitOp (GetField [NamedField field params]) (Var v) t
          e -> error $ "Compiler error: unexpected case in convertE: " ++
               show e
        cleanup :: (E -> Convert Var) -> E -> Convert Var
        cleanup hdlr e = do
          scope <- getScope
          v <- hdlr e
          setScope $ v:scope
          return v
--Gets the scope
getScope :: Convert [Var]
getScope = gets csScope
--Sets the scope of Core Vars that will be passed to the next stmt (alongside
--the env). It determines which vars are on the stack when you branch and
--has no effect for straight-line stmts, but since we don't know in advance
--whether the next stmt is branched to we always set it.
setScope :: [Var] -> Convert ()
setScope scope = modify (\s->s{csScope = scope})
          
--Collect the stmts emitted by a Convert action, returning them instead of
--appending them to the state.
--Note csOutput is accumulated in reverse order, so it must be reversed before
--returning it.
collect :: Convert a -> Convert (a,[Stmt])
collect c = do
  s <- get
  put s{csOutput = []}
  a <- c
  s' <- get
  put s'{csOutput = csOutput s}
  return (a, reverse $ csOutput s')

--Each emitted stmt must be preceded by a scope declaration.
--That is the state of the stack before the stmt, rather than the scope it
--needs.
--Note stmts are stored in reverse order and must be reversed when collected
--into a block.
emitStmt :: Stmt -> Convert ()
emitStmt stmt = do
  s <- get
  let output = csOutput s
      scope = csScope s
  put s{csOutput = stmt : IR.Declare scope : output}

--Emits a Core op, binding its result to a single new var. Doesn't specify
--the stack/scope effect.
--It takes its result type as a parameter to give to the Var.
--Note: side-effecting ops may return a tuple containing a mix of dynamic
--and state types. Pair must then be able to store a mix of them, so state
--types are of kind Type!
--Consequence: not all Types are coerce#ible to Bytestring#.
emitOp :: PrimOp -> Value -> T -> Convert Var
emitOp op val t = do
  v <- cNewVar t
  emitStmt (Var v IR.:= OpE (op,val))
  return v

--Returns the type of an E; if the type is determined by a parameterized name
--(e.g. f, g, Con) it must unfortunately be computed rather than retrieved
--from a cache in the AST itself.
--Precondition: the E has already been HM'd and monomorphized.
cTypeOf :: E -> Convert T
cTypeOf = \case
  EInteger _ -> return $ UInt 32
  TypedVar (Just t) _ -> return t
  f :$ _ -> do
    tf <- cTypeOf f
    let a :-> b = tf
    return a
  EArray (Just t) es -> return $ Array (fromIntegral $ length es) t
  TyApp nm ts -> do
    mod <- cGetModule
    let Just (vs,t) = M.lookup nm $ tysigs mod
        Right monoT = instT (M.fromList $ zip vs ts) t
    return monoT
  CaseE {} -> error "No syntactic support yet..."
  OPAssign _ p _ _ -> gop p
  PPPre p -> gop p
  PPPost p -> gop p
  MMPre p -> gop p
  MMPost p -> gop p
  ConRecord con (Just params) _fields -> typeOfConE con params
  Dot _ (Just params) field -> typeOfDotE field params
  where gop = cTypeOfP
--The type of a monomorphized pattern
cTypeOfP :: Pat -> Convert T
cTypeOfP = \case
  PWild (Just t) -> return t
  TypedPVar (Just t) _ -> return t
  Deref (Just [_r,a]) _ -> return a
  PArray (Just t) ps -> return $ Array (fromIntegral $ length ps) t
  --Look up field info, then parent constructor; get polytype of field,
  --then instantiate using params in dt info.
  PDot (Just params) _ field -> typeOfDotE field params
  PBang (Just [_len,a]) _ _ -> return a
  --Look up con info to get rhs, then instantiate using params in dt info
  PCon con (Just params) _ -> typeOfConE con params

--Given a field and its type params, returns the type of a well-typed
--e.field@params.
--Invariant: all boxed fields have been desugared away.
--Do I still store field signatures? Don't use them for now...
--TODO use cached signatures.
--Note: dtRegion in DTInfo makes dtBoxed superfluous.
typeOfDotE :: Name -> [T] -> Convert T
typeOfDotE field params = do
  mod <- cGetModule
  let dtsi = dtsInfo mod
      Just fi = M.lookup field $ fieldInfo dtsi
  case fi of
    IsTag False tycon ->
      let Just dti = M.lookup tycon $ datatypes dtsi
          ts = dtTagScheme dti
      in case ts of
           Nil -> error $ "Compiler error: tag of untagged DT " ++ tycon
           N1 len -> return $ UInt $ fromIntegral len
           N16 -> return $ UInt 1
           Custom t _ ->
             --Now we need to instantiate the t
             let vs = dtParams dti
                 v2t = M.fromList $ zip vs params
                 Right monoT = instT v2t t
             in return monoT
    IsNormal False tycon con ->
      let Just ci = M.lookup con $ conInfo dtsi
          Just fieldT = lookup field $ conFields ci
          Just dti = M.lookup tycon $ datatypes dtsi
          vs = dtParams dti
          v2t = M.fromList $ zip vs params
          Right monoT = instT v2t fieldT
      in return monoT
    fi | fiBoxed fi -> error $ "Compiler error: unexpected boxed field in "
                       ++ "typeOfDotE: " ++ field ++ " " ++ show params

--Given a Con and its params, returns the type of a well-typed Con{...} record.
--Precondition: the Con is unboxed (the boxed ones should've been desugared
--away).
typeOfConE :: Name -> [T] -> Convert T
typeOfConE con params = do
  mod <- cGetModule
  let dtsi = dtsInfo mod
      Just ci = M.lookup con $ conInfo dtsi
      conT = conRHS ci
      tycon = conParent ci
      Just dti = M.lookup tycon $ datatypes dtsi
      vs = dtParams dti
      v2t = M.fromList $ zip vs params
      Right monoT = instT v2t conT
  if conBoxed ci
    then error $ "Compiler error: unexpected boxed con in typeOfConE: " ++
         con ++ " " ++ show params
    else return monoT

--Gets the Module, which contains much of the info necessary for compilation
cGetModule :: Convert Module
cGetModule = do
  (mod,_mono,_ser) <- ask
  return mod

--evalPatternEs converts a syntactic pattern which may contain subexprs such
--as (arr!ix(), (*p()).field) to
--x <- ix(), y <- p()
--(arr!x,(*y).field).
--That's necessary to prevent e.g. (arr!ix())++ from evaluating ix() twice.
--Iff the pattern is trivial (equivalent to _), it returns Nothing.
--EvaluatedPats are normalized and nonsensical patterns (e.g. _.field or
--Con{}.field) raise an exception.
evalPatternEs :: Pat -> Convert (Maybe EvaluatedPat)
evalPatternEs = go
  where go = \case
          PWild _ -> return Nothing
          PArray (Just t) ps -> do
            meps <- mapM go ps
            let ixeps = [(ix,ep) | (ix,Just ep) <- zip [0..] meps]
            return $ if null ixeps
                     then Nothing
                     else Just $ EPArray (length meps) t ixeps
          PCon con (Just params) field_ps ->
            error "todo"
          --Remaining valid form: (local|deref)(.field | !ix)* 
          p -> evalIndexPatternEs p
--First roll into (Either Var E, [Either .field !E])
--If local: eval the ix Es in order to get [Field]
--If *ptr: eval the ptr first, then eagerly transform it using the fields and
--indices.
evalIndexPatternEs :: Pat -> Convert (Maybe EvaluatedPat)
evalIndexPatternEs = go
  where go = \case
          _ -> error "todo"

--A pattern after exprs have been evaluated.
--Its form is restricted to preclude Con{..} (.field | !ix)* which is
--nonsensical.
--BCon {bfield: p} => Unbox (UBCon {ubfield: p})
data EvaluatedPat = EPLocal Var [Field]
                  --Locals become vars in Structured; they're still viewed as
                  --mutable in the abstraction because it's pre-SSA
                  | EPDeref Var --the fields have been baked into the ptr
                  --The Bool is to tell whether the tag needs to be checked
                  --(it does not in cases).
                  | EPCon Bool Name [T] [(Name,EvaluatedPat)]
                  | EPArray Int T [(Int,EvaluatedPat)]
                  | Unbox EvaluatedPat
  deriving (Eq,Ord,Read,Show)
--Refutable patterns in cases don't need to check the tag of the top-level con
--(it's already been determined to match via case branching).
elideTagCheck :: EvaluatedPat -> EvaluatedPat
elideTagCheck (EPCon check con ts fs) = EPCon False con ts fs
elideTagCheck ep = ep

--An eval'd pat has two uses: assigning a value to it and interpreting it as
--an E.
--Problem: what about boxed constructors? Evaluating an eval'd pat should
--consistently produce the same value and have no side effects.
--Consider (Nil :: List ()) |= 0x10_00_00
--Solution: disallow boxed constructors in evaluatedPat2Value; it should only
--permit the permissible patterns for += and ++,
--i.e. local(.field | !v)* | *v
evaluatedPat2Value :: EvaluatedPat -> Convert Var
evaluatedPat2Value = error "todo"

--assign implements matching of a pattern p to a value (var) v.
--It's central to pattern matching in case and assignment operations.
--In contrast to Haskell, EVMC case supports only one-level case distinction;
--subpatterns are matched using assign and will revert rather than go to the
--next candidate pattern if they fail. That's to avoid the problem of
--selecting an efficient matching order in composite patterns (for now).
{-Behavior:
Con{field: p} = v =>
 if Con is boxed:
  ImplTyCon ptr = v
  ImplCon{implTyCon_field: p} = *ptr
 else: case tag scheme Con of
  Nil: return ()
  other: require v's tag == Con's tag
 for (field,p) in pattern: p = v.field
TODO opt: if mem remains the same, (*p).field ~ *(GetPtrField p field)
TODO boxed con pattern => deref mentioned

.field | !ix have different behavior for locals and derefs; I should convert
*p (.field | !ix)* to a single *v in the abused pattern.
However, local!foo()!bar() needs to save both foo and bar.
Ideally I'd just save a slice offset (essentially a byte pointer into a
stack var).
-}
assign :: EvaluatedPat -> Var -> Convert ()
assign ep v = error "todo"
            
--The array creation op on vars (evaluated exprs).
--FW: eagerly compress at the word level, as otherwise the stack could grow
--large.
--When assigning a large array literal to a pointer, it would also be worth
--eagerly writing.
primMkArray :: T -> [Var] -> Convert Var
primMkArray = error "todo"

--Converts a list of vars to a tuple value
vars2value :: [Var] -> Value
vars2value = foldr Pair Unit . map Var

--Emits a call (ret = f x). However, it also needs to pass and take the env to
--encode side effects! Passing the env is done after Structured, because
--before passing everything I must create the return continuation.
--The Value may be a tuple.
call :: Var -> Value -> Convert Var
call vf vx = do
  let Mono _ (a :-> b) = vf
  retv <- cNewVar b
  --(retv,env) = Call vf vx 
  let retLHS = Pair (Var retv) (Pair envV Unit)
  emitStmt (retLHS IR.:= Call vf vx)
  return retv
--Calls a C function with the given name and typarams.
--It must be mentioned in Mono.
callCFun :: Name -> [T] -> Value -> Convert Var
callCFun f params val = do
  (_,monoS,_) <- ask
  case M.lookup (f,params) $ exploredFuns monoS of
    Nothing -> error $ "Compiler error: function " ++ f ++ " " ++ show params
               ++ " not mentioned despite use in callCFun!"
    Just (ft, _) -> do
      fv <- emitOp (Const ft $ MkConst $ TyApp f params) Unit ft
      call fv val

--Deduplicates the logic for ++_ et al
--Parameters: inc (++) or dec (--), old or new value returned
plusplus :: Name -> Bool -> Pat -> Convert Var
plusplus incdec prefix p = do
  mp' <- evalPatternEs p
  p' <- case mp' of
          Nothing -> throwError $
                     PlusPluslikeOnWildlikePattern incdec prefix p
          Just p' -> return p'
  old <- evaluatedPat2Value p'
  let t = typeOfVar old
      opf = TyApp incdec [t]
  vf <- convertE opf
  new <- call vf (Var old)
  assign p' new
  return $ if prefix
           then old
           else new
