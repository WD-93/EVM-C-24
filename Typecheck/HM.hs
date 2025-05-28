{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module TypeCheck.HM where

import Util
import AST.DTs
import TypeCheck.TySyn (tyVars,tyCons)
import TypeCheck.FIKS (splitTyFun)
import TypeCheck.DependencyGraph (buildGraph)

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Generics (everywhere,everywhereM,mkT,mkQ,mkM,everything)
import Control.Arrow ((***))

--A new attempt at Hindley-Milner type checking
--Scoped type variables and (->) introduce complexity; type and kind inference
--must be done simultaneously.

--Possible sources of errors or nontermination:
--Infinite types, t ~ Con t
--An infinite hierarchy of kinds; it's limited to 3 levels:
--1: Memory, Word etc
--2: Region, Type etc
--3: Kind (the root, has no kind)

{-
Kinding tycons other than (->):
Look its kind up in kindsigs, return it

Kinding allocated tyvar a:
Look it up in hmTyVars, zonk 

Kinding t1 :$$ t2:
k1 <- kindOf t1
k2 <- kindOf t2
Allocate new kind vars b, unify k1 with k2 -> b; return b

Kinding (->):
Unify args with Type, return Type

TyNat:
return Nat

Useful invariant: the tyvar and kind var map is one level deep,
with each rhs of the form T<vars> where all vars are unbound.
That requires 
-}

{-
Typing E:

EInteger:
return Word
--Desugaring changes semantics: before n :: Int s len, but it's converted to
--fromWord (n :: Word) :: Int s len

Var nm:
If local, look up its type

If a function and in current SCC, look up its (monomorphic) type

If a function and not in current SCC, look up polymorphic type signature pt in
tysigs.
vars, t <- quantify pt
return nm ty applied to vars, t

-}

--The type inference monad is run a SCC at a time in topological order.
--Read-only state:
--Kind signatures
--Constructor types
--Field types
--Signatures for things which have already been annotated or have tysigs
--Note: static values and globals also need to be part of the SCC tree!
--a -> b in the SCC graph if a mentions b in its definition;
--global g -> a if a mentions g in its definition, since a global's type
--is inferred from its uses.

{-Overall algo:
tysigs:
Check each nm : t corresponds to a definition (fun, static, global)
and t has kind Type.
kindsigs: Check each kind is well-kinded.
In both cases, default unbound kind vars to Type.
constructors: check the type is of kind Type

Separate out the vals with signatures; make a usage graph of the rest and SCC
it. Infer the types of SCCs in topological order.
Finally, check the vals with sigs match their signatures.

End result: every function (constructors and fields included) are annotated
with their type applications, polymorphism is explicit.

Infer function f pat = s
Declare locals for the vars in pat:
 If a var is a function other than deref, that's an error
 If it's a constructor or field, ignore
a <- typeOf pat
b <- newTyVar
inferS b s
return (a -> b)

Value name types:
Fun, static, global
Constructor, field --don't need to be typed
local --in state
unbound

Without eager propagation of var -> t binds (e.g. via v -> T a b subscribing
to binds of a or b), all vars need to be zonked at the end, alongside
defaulting.

When a value f has a signature t, unify its inferred type with t.
If each variable in vars t does not bind to a unique tyvar, fail with
"rigid type variable can't be constrained".
Default only those unbound vars which vars t don't bind to.

Restrict the max depth of the sort hierarchy to 3, e.g.
Memory :: Region :: Kind.
Kind itself should have no kind to avoid Girard's paradox or looping;
treat TyCon : Kind specially, disallow any other mention of Kind.

Hierarchy:
level 1: Memory, value types...
level 2: Region, Type...
level 3: Kind
Except for level 2 : Kind definitions, a kindsig rhs may only consist of level 2
terms.
Foo : (Word -> Word) -> Type or Memory -> Type is forbidden, for example
Consequence: the kind of (->) should not be ambiguous; in a level-1 context
it's Type -> Type -> Type and in level 2 it's Kind -> Kind -> Kind (i.e. it
doesn't need to be checked because everything is Kind).

Accidental power:
NatList : Kind
Nil: NatList
Cons : Nat -> NatList -> NatList
NLProxy : NatList -> Type
knownValue : NatProxy n -> Word --would need to be primitive
Now I can statically pass [Word]s... does that create problems?
-}
data HMR = HMR {
  --Things with sigs or already typed; includes constructors and fields
  hmTySigs :: Map Name T,
  --The kind of level-1 tycons
  hmKindSigs :: Map Name T,
  --The set of level-2 tycons; they're all of kind Kind
  hmSorts :: Set Name,
  --The tyvar tau to which each dynamic thing in the SCC is mapped.
  hmTaus :: Map Name Name,
  --Local -> tyvar; unused during kind and sv check
  hmLocals :: Map Name Name --local -> tyvar
  }
data HMS = HMS {
  hmVarCounter :: Int, --used for allocating ty and kind vars
  --The maps are one level deep; vars only refer to types
  --containing unbound vars.
  --zonk to lazily normalize; if a var refers to itself that's
  --an error.
  hmTyMap :: Map Name T,
  --A map from kind var to the kind it's equal to
  hmKindMap :: Map Name T,
  --The sets of ty and kind vars need to be tracked to
  --detect and default unbound ones.
  --The set of tyvars in scope. They come from allocation
  --($anonN) and explicit tyvars.
  --Each is initially associated with a kind var;
  --it should get zonked on lookup.
  hmTyVars :: Map Name T,
  --Kind vars come only from allocation; there are no explicit
  --kind vars.
  hmKindVars :: Set Name,
  --Explicit tyvars as found in e :: List r a.
  --They're associated with an allocated tyvar in hmTyVars.
  scopedTyVars :: Map Name Name
  } deriving (Eq,Ord,Read,Show)
data HMError = Can'tConstructTheInfiniteType Name T --t ~ T a
             | Can'tUnify T T
             | NonTypeInArrow T T
             --Only an error after inference:
             | KindVarUnbound Name
             --The result of looking up the tau of a non-scc name
             | TauOfNonSCCMember Name
  deriving (Eq,Ord,Read,Show)
--Including the HM state in the error message may be helpful, so we place
--the Except innermost
--Alt approach: a module as state, incrementally update functions, tysigs and
--statics.
type HM = ReaderT HMR (ExceptT HMError (State HMS))
runHM :: HM a -> HMR -> HMS -> (Either HMError a, HMS)
runHM hm hmr hms =
  runState (runExceptT (runReaderT hm hmr)) hms
data TCModuleError = InCheckTySig Name SigError
                   | InCheckKindSig Name KindSigError
                   | InCheckDatatype Name DatatypeError
                   | TysigsMandatoryForUnitializedGs [Name]
                   | KindMayHaveNoKind
                   | InInferSCC [Name] (HMError,HMS)
  deriving (Eq,Ord,Read,Show)
data SigError = MissingDefinition
              | BadKindInSig T (HMError,HMS)
              | PolymorphicTySigInMonoThing T
              deriving (Eq,Ord,Read,Show)
data KindSigError = KindOutOfScope Name
                  | KindAppliedToKind T T
                  | TyNatInL2Context Integer
                  | TyVarInSimplyKindedContext Name
  deriving (Eq,Ord,Read,Show)
data DatatypeError = InConstructor Name ConstructorError
  deriving (Eq,Ord,Read,Show)
data ConstructorError = InNthArgument Int ConstructorArgumentError
  deriving (Eq,Ord,Read,Show)
data ConstructorArgumentError = TyVarsNotInScope (Set Name)
                              | HMErrorInCon (HMError,HMS)
  deriving (Eq,Ord,Read,Show)
tcModule :: Module -> Either TCModuleError Module
tcModule m = do
  tcTysigs m
  tcKindsigs m
  tcDatatypes m
  tcGlobals m
  complainIf (S.member "Kind" $ S.union (M.keysSet $ kindsigs m)
               (sorts m))
    KindMayHaveNoKind
  m' <- inferTypes m
  return m'

--Just checks each global without an initializer has a signature
tcGlobals :: Module -> Either TCModuleError ()
tcGlobals m = do
  let offenders = do
        (g,(r,me)) <- M.toList $ globals m
        if (me /= Nothing) && not (M.member g $ tysigs m)
          then []
          else return g
  complainIf (not $ null offenders)
    $ TysigsMandatoryForUnitializedGs offenders

--For each TyCon params, bind the params to the kinds given by TyCon's kind
--then unify each arg's kind with Type.
--data Con a = Con b is an error; unification may not add new tyvars to scope
--To maintain the invariant that unify doesn't expect any tyvars not bound
--to a kind, check for out of scope vars first.
--As before, check for no unbound kind vars with allKindsBound.
tcDatatypes :: Module -> Either TCModuleError ()
tcDatatypes m = do
  let dts = M.toList $ datatypes m
      hmr = newHMR{hmKindSigs = kindsigs m,
                   hmSorts = sorts m
                  }
  mapM_ (\(tycon,(params,condecls)) -> (do
           --Note duplicate params have been ruled out earlier
           let k = kindsigs m M.! tycon
           --FIKS also guarantees tycon is in kindsigs, its arity matches
           --params and the return kind is Type
           let (kargs,_) = splitTyFun k
               param2kind = M.fromList $ zip params kargs
               paramSet = S.fromList params
               hms = newHMS{hmTyVars = param2kind}
           mapM_ (\(con, ei_ts_fields) -> (do
                    let ts = case ei_ts_fields of
                               Left ts -> ts
                               Right nmts -> map snd nmts
                    mapM (\(nth,t) -> (
                             do let outOfScope = S.difference (tyVars t)
                                                 paramSet
                                complainIf (not $ S.null outOfScope)
                                  $ TyVarsNotInScope outOfScope
                                case runHM (do k <- kindOf t
                                               unifyK k "Type"
                                               allKindsBound
                                           ) hmr hms of
                                  (Left hme, s) -> Left $ HMErrorInCon (hme,s)
                                  (Right _, _) -> return ()
                             )
                         ? InNthArgument nth) $ zip [1..] ts)
                   ? InConstructor con)
             condecls)
          ? InCheckDatatype tycon) dts

--For each Nm : k, check k is well-kinded
--What can go wrong?
--Since the rhs is level 2, all user-defined level-2 kinds are : Kind
--(and thus unparameterized) and the only combinator (->) is always fully
--applied... 1) scope errors, 2) tycon applied to tycon, 3) tyvars.
--Have they already been caught by TySyn?
tcKindsigs :: Module -> Either TCModuleError ()
tcKindsigs m =
  mapM_ (\(tycon,k) -> go k ? InCheckKindSig tycon) $
  M.toList $ kindsigs m
  where go = \case
          k1 :-> k2 -> go k1 >> go k2
          k1 :$$ k2 -> throwError $ KindAppliedToKind k1 k2
          TyNat n -> throwError $ TyNatInL2Context n
          TyCon nm
            | S.member nm (sorts m) -> return ()
            | let -> throwError $ KindOutOfScope nm
          TyVar nm -> throwError $ TyVarInSimplyKindedContext nm
--For each nm : t, check nm corresponds to a defun, static or global;
--check t :: Type
--Can I do that? return : a -> m a poses no problem.
--transformContainer : f a -> g a OTOH...
--Solution: disallow kind polymorphism, require kinds are bound in signatures.
--Also require all kind (meta)variables are bound after inference; do not
--default them.
--If the nm is a static or global, it must be monomorphic.
tcTysigs :: Module -> Either TCModuleError ()
tcTysigs m = do
  let sigs = tysigs m
  mapM_ go $ M.toList sigs
    where go (nm,t) = (case () of
                         _ | S.member nm $ S.union (M.keysSet $ static m) $
                             M.keysSet $ globals m -> do
                               complainIf (polymorphic t)
                                 $ PolymorphicTySigInMonoThing t
                               checkIsType m t
                           | M.member nm $ defuns m ->
                             checkIsType m t
                           | otherwise -> throwError MissingDefinition
                      )
                  ? InCheckTySig nm

--Checks T has any tyvars
polymorphic :: T -> Bool
polymorphic = not . S.null . tyVars
--Given a module m, initializes HM, instantiates t and checks it is :: Type
--Relevant module fields: kindsigs
checkIsType :: Module -> T -> Either SigError ()
checkIsType m t = (case runHM go newHMR{hmKindSigs = kindsigs m,
                                 hmSorts = sorts m
                                }
                        newHMS
                    of
                      (Left err, s) -> Left (err,s)
                      (Right res, _) -> Right res
                  ) ? BadKindInSig t
  where go = do
          (nms,t') <- quantify t --introduce new tyvars bound to kind vars
          k <- kindOf t'
          unifyK k "Type"
          --There should be no polymorphic kind variables
          allKindsBound

--Templates to initialize with the fields you need
newHMR = HMR {hmTySigs = e,
              hmKindSigs = e,
              hmSorts = S.empty,
              hmTaus = M.empty,
              hmLocals = e
             }
  where e :: Map k v
        e = M.empty
newHMS = HMS {hmVarCounter = 0,
              hmTyMap = e,
              hmKindMap = e,
              hmTyVars = e,
              hmKindVars = S.empty,
              scopedTyVars = e
             }
  where e :: Map k v
        e = M.empty

--Returns the expr (updated with tyapps on funs) 
typeOf :: E -> HM (E,T)
typeOf = go
  where go = \case
          EInteger n -> return (EInteger n, UInt 256)
          f :$ x -> do
            (f',tf) <- go f
            (x',tx) <- go x
            b <- newTyVar
            unify tf (tx :-> b)
            return (f' :$ x', b)
          --Note the type annotation is erased; it's superfluous after type
          --application.
          e ::: t -> do
            (e',te) <- go e
            t' <- scopeType t
            unify te t'
            kte <- kindOf te
            unifyK kte "Type" --all value types are of kind Type
            return (e',te)
          p := e -> do
            (p',tp) <- go p
            (e',te) <- go e
            unify tp te
            return (p' := e', te)
          EArray es -> do
            a <- newTyVar
            e'ts <- mapM go es
            let e's = map fst e'ts
                ts = map snd e'ts
                len = length es
            mapM_ (unify a) ts
            return (EArray e's, Array (TyNat $ fromIntegral len) a)
          TyApp e t -> error "Compiler error: TyApp should not appear yet!"
          --Now for the tricky bit...
          --If _, return _ @ a; it's the only polymorphic non-function.
          --If in tysigs, quantify and return that
          --If in locals, return the associated tyvar (zonked)
          --If in SCC, return associated tyvar (zonked)
          --Otherwise, fail with scope error
          Var nm -> do
            hmr <- ask
            case () of
              _ | nm == "_" -> do
                    v <- newTyVar
                    k <- kindOf v
                    unifyK k "Type"
                    return (TyApp "_" [v], v)
                | Just scheme <- M.lookup nm $ hmTySigs hmr -> do
                  (vars,t) <- quantify scheme
                  return (TyApp nm $ map TyVar vars, t)
                | Just v <- M.lookup nm $ hmLocals hmr -> do
                  t <- zonk $ TyVar v
                  return (Var nm, t)
                | Just v <- M.lookup nm $ hmTaus hmr -> do
                    t <- zonk $ TyVar v
                    return (Var nm, t)
--Associate each tyvar not yet in scopedTyVars with a fresh tyvar.
--Returns a type containing only allocated tyvars.
scopeType :: T -> HM T
scopeType = everywhereM (mkM handleScopedVar)
handleScopedVar :: T -> HM T
handleScopedVar = \case
  TyVar nm -> do
    mv <- gets (M.lookup nm . scopedTyVars)
    case mv of
      Just v -> return $ TyVar v
      Nothing -> do
        v <- newTyVar
        let TyVar vnm = v
        modify (\s->s{scopedTyVars=M.insert nm vnm $
                       scopedTyVars s})
        return v
  t -> return t
          
--The kind of a given type
kindOf :: T -> HM T
kindOf = \case
  --(->) is always Type -> Type -> Type in this context
  --It's also only ever fully applied.
  a :-> b -> do
    ka <- kindOf a
    unifyK ka "Type"
    kb <- kindOf b
    unifyK kb "Type"
    return "Type"
  TyCon nm -> do
    mk <- asks (M.lookup nm . hmKindSigs)
    case mk of
      Nothing -> error $ "Compiler error: tycon " ++ show nm ++ " not in scope "
                 ++ "despite FIKS"
      Just k -> return k
  --Each tyvar maps to a kind... but what about when you need to recursively
  --get kindOf for kf kx or a -> b?
  --Memory :: Region :: Kind
  --If I restrict kind hierarchies to max depth 3 (ending in kind), maybe I
  --can avoid infinite recursion
  TyVar a -> do
    kv <- (M.! a) <$> gets hmTyVars
    zonkK kv
  TyNat _ -> return "Nat"
  tf :$$ tx -> do
    kf <- kindOf tf
    kx <- kindOf tx
    b <- newKindVar
    unifyK kf (kx :-> b)
    return b

--Adding a hint to make it easier to identify the origin of type errors in
--source.
newVar = newVarNamed ""
newTyVar = newTyVarNamed ""
newKindVar = newKindVarNamed ""
newVarNamed :: Name -> HM Name
newVarNamed hint = do
  s <- get
  let n = hmVarCounter s
      v = "$" ++ hint ++ "_" ++ show n
  put s{hmVarCounter = n + 1}
  return v
newTyVarNamed :: Name -> HM T
newTyVarNamed hint = do
  v <- newVarNamed hint 
  k <- newKindVar
  modify (\s->s{hmTyVars = M.insert v k $ hmTyVars s})
  return $ TyVar v
newKindVarNamed :: Name -> HM T
newKindVarNamed hint = do
  v <- newVarNamed hint
  modify (\s->s{hmKindVars = S.insert v $ hmKindVars s})
  return $ TyVar v
--If t1 ~ t2, kindOf t1 = kindOf t2
--If a ~ b, bind min a b to max a b
--Zonking before unification isn't sufficient: consider (a,Bool) ~ (Int,a)
--But zonking at every step is exp-time...
unify :: T -> T -> HM ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  k1 <- kindOf t1'
  k2 <- kindOf t2'
  unifyK k1 k2
  case (t1',t2') of
    (TyVar a, TyVar b)
      | a == b -> return ()
      | let -> bindVar (min a b) $ TyVar $ max a b
    (TyVar a, t) -> bindVar a t
    (t, TyVar a) -> bindVar a t
    (tf :$$ tx, tg :$$ ty) -> do
      unify tf tg
      unify tg ty
    _ -> complainIf (t1' /= t2')
         $ Can'tUnify t1' t2'
bindVar :: Name -> T -> HM ()
bindVar a t = do
  let vs = tyVars t
  complainIf (S.member a vs)
    $ Can'tConstructTheInfiniteType a t
  modify (\s->s{hmTyMap=M.insert a t $ hmTyMap s})
bindVarK :: Name -> T -> HM ()
bindVarK a t = do
  let vs = tyVars t
  complainIf (S.member a vs)
    $ Can'tConstructTheInfiniteType a t
  modify (\s->s{hmKindMap=M.insert a t $ hmKindMap s})
unifyK :: T -> T -> HM ()
unifyK k1 k2 = do
  k1' <- zonkK k1
  k2' <- zonkK k2
  case (k1',k2') of
    (TyVar a, TyVar b)
      | a == b -> return ()
      | let -> bindVarK (min a b) $ TyVar $ max a b
    (TyVar a, k) -> bindVarK a k
    (k, TyVar a) -> bindVarK a k
    (kf :$$ kx, kg :$$ ky) -> do
      unifyK kf kg
      unifyK kx ky
    _ -> complainIf (k1' /= k2')
         $ Can'tUnify k1' k2'

--Constructing the dependency graph of funs, statics, globals.
--Names with sigs are excluded.

--Instantiate new tyvars for a type scheme
--The kind check is done later.
--To know which tyvars to apply and in what order, we also return the list of
--new tyvars.
--TODO: record the kinds of tyvars in signatures, immediately unify with
--them rather than re-inferring.
quantify :: T -> HM ([Name],T)
quantify t = do
  let vs = tyVarsList t
  fresh <- map (\(TyVar v) -> v) <$> mapM newTyVarNamed vs
  let v2fresh = M.fromList $ zip vs fresh
  return (fresh,substTyVarNames v2fresh t)

--Converts a var to normal form, substituting any bound var for its rhs
--and updating the tyvar map at the same time.
--Will diverge if there's a loop a ~ T<a>, so need to check for cycles on var
--binding.
zonk :: T -> HM T
zonk = \case
  TyVar nm -> do
    mt <- gets (M.lookup nm . hmTyMap)
    case mt of
      Nothing -> return $ TyVar nm
      Just t -> do
        t' <- zonk t
        modify (\s->s{hmTyMap = M.insert nm t' $ hmTyMap s})
        return t'
  tf :$$ tx -> (:$$) <$> zonk tf <*> zonk tx
  t -> return t
--Ditto for kind vars; todo compress with combinator
zonkK :: T -> HM T
zonkK = \case
  TyVar nm -> do
    mt <- gets (M.lookup nm . hmKindMap)
    case mt of
      Nothing -> return $ TyVar nm
      Just t -> do
        t' <- zonkK t
        modify (\s->s{hmKindMap = M.insert nm t' $ hmKindMap s})
        return t'
  tf :$$ tx -> (:$$) <$> zonkK tf <*> zonkK tx
  t -> return t

--A post-inference check; kind polymorphism is not permitted
allKindsBound :: HM ()
allKindsBound = do
  kvs <- S.toList <$> gets hmKindVars
  mapM_ (\kv -> do
            k2k <- gets hmKindMap
            case M.lookup kv k2k of
              Nothing -> throwError $ KindVarUnbound kv
              Just _ -> return ()) kvs

--First, separate out dynamic things with tysigs and construct the dependency
--graph.
inferTypes :: Module -> Either TCModuleError Module
inferTypes m = do
  let nmss = buildGraph m
  go m nmss
  where go m = \case
          [] -> return m
          nms:nmss -> do
            m' <- inferSCC nms m ? InInferSCC nms
            go m' nmss
type InferSCC = Either (HMError,HMS)
--Invariant: every mentioned name but locals and the scc names have already
--been given type signatures.
--For each name, allocate a tyvar tau and unify its kind with Type.
--For each function f -> tau, unify typeOfFun f with tau
--For each static s := e -> tau, unify typeOf e with tau
--If any unbound kind vars remain, fail.
--Unify any unbound type vars not in the vars of the zonked taus with Word.
--If any static or global is still polymorphic, fail.
--Add prettified type signatures for all names
--Update definitions of functions and statics.
--Wrong: globals should have definitions as well!
inferSCC :: [Name] -> Module -> InferSCC Module
inferSCC nms m =
  case runHM go hmr newHMS of
    (Left hme, s) -> Left (hme,s)
    --Updated definitions and new tysigs
    (Right (sigs,funs,stats,globs), _) ->
      return m{tysigs = M.union sigs $ tysigs m,
               defuns = M.union funs $ defuns m,
               static = M.union stats $ static m,
               globals = M.union globs $ globals m
              }
  where hmr = HMR{hmTySigs = tysigs m,
                  hmKindSigs = kindsigs m,
                  hmSorts = sorts m,
                  hmTaus = M.empty, --We'll set them in shortly
                  hmLocals = M.empty
                 }
        go = do
          --Allocate new taus :: Type for each nm in scc
          taus <- mapM newTyVarNamed $ map ("tau_" ++) nms
          mapM (\v -> do
                   k <- kindOf v
                   unifyK k "Type") taus
          let nm2tau = M.fromList $ zip nms $ map (\(TyVar v) -> v) taus
          withReaderT (\hmr->hmr{hmTaus=nm2tau}) $ do
            --For each nm in nms, infer type to get an updated definition and
            --unify the type with tau
            (funs,stats,globs) <- inferDefs m nms
            --Zonk taus; if any static or global is polymorphic fail
            --return nm->zonked and prettified tau and updated defs
            error "todo"

--Returns updated definitions for functions, statics and globals;
--their type is returned by unifying it with tau
inferDefs :: Module -> [Name] -> HM (Map Name (Pat,S),
                                     Map Name E,
                                     Map Name (Region, Maybe E))
inferDefs m = go
  where go = \case
          [] -> return (M.empty,M.empty,M.empty)
          nm:nms -> do
            (funs,stats,globs) <- go nms
            case () of
              _ | Just pats <- M.lookup nm $ defuns m -> do
                    (pats',t) <- typeOfFun pats
                    unify t <$> tauOf nm
                    return (M.insert nm pats' funs,stats,globs)
                | Just e <- M.lookup nm $ static m -> do
                    (e',t) <-  typeOf e
                    unify t <$> tauOf nm
                    return (funs,M.insert nm e' stats, globs)
                | Just (r,Just e) <- M.lookup nm $ globals m -> do
                  (e',t) <- typeOf e
                  unify t <$> tauOf nm
                  return (funs,stats,M.insert nm (r,Just e') globs)
                | otherwise -> error "This should never happen"

tauOf :: Name -> HM T
tauOf nm = do
  nm2v <- asks hmTaus
  case M.lookup nm nm2v of
    Just v -> return $ TyVar v
    Nothing -> throwError $ TauOfNonSCCMember nm
--First need to declare new locals for the locals in pat
--Pat structure:
--Con pats, Con {field: p, ...}
-- .field p
--global, local, _
typeOfFun :: (Pat,S) -> HM ((Pat,S),T)
typeOfFun (pat,s) = error "todo"

--Assigns a pretty tyvar from a,b..z, a1,b1..z1 for each tyvar in order of
--occurrence.
prettifyType :: T -> T
prettifyType t =
  let vs = tyVarsList t
      v2p = M.fromList $ zip vs pretties
  in substTyVarNames v2p t
  where pretties = [[c] | c <- ['a'..'z']] ++
                   (do n <- [1..]
                       c <- ['a'..'z']
                       return $ c : show n
                   )
substTyVarNames :: Map Name Name -> T -> T
substTyVarNames = substTyVars . M.map TyVar
substTyVars :: Map Name T -> T -> T
substTyVars v2t = everywhere (mkT $ \case TyVar v
                                            | Just t <- M.lookup v v2t -> t
                                          t -> t)

--Gathers all mentioned tyvars and returns them in order of first mention
tyVarsList :: T -> [Name]
tyVarsList = fst . tyVarsListSet
tyVarsListSet :: T -> ([Name],Set Name)
tyVarsListSet = everything (\(nms1,snms1) (nms2,snms2) ->
                              (nms1 ++ filter (not . flip S.member snms1) nms2,
                               S.union snms1 snms2)) $ mkQ ([],S.empty) $
                \case TyVar nm -> ([nm],S.singleton nm)
                      _ -> ([],S.empty)
