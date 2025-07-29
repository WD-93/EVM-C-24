{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Typecheck.HM where

import Util
import AST.DTs
import AST.Util (freeVarsPat,op2fun,region2T)
import Typecheck.TySyn (tyVars,tyCons,
                        --TODO move the two functions below to a more
                        --appropriate module
                        everywhereButStopM,isT)
import Typecheck.FIKS (splitTyFun)
import Typecheck.DependencyGraph (buildGraph)
import Typecheck.HM.AddConsAndFieldsToTySigs (addConsAndFieldsToTySigs)

import Data.Map (Map(..))
import qualified Data.Map as M hiding ((!))
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Generics (everywhere,everywhereM,mkT,mkQ,mkM,everything,Data(..))
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
  --New: dtsInfo from module, using which Con {field: e/p} can be typed
  hmDTsInfo :: DTsInfo E,
  --The kind of level-1 tycons
  hmKindSigs :: Map Name T,
  --The set of level-2 tycons; they're all of kind Kind
  hmSorts :: Set Name,
  --Default instance for level-2 tycons (non-mandatory); from defaults in
  --Module.
  hmDefaults :: Map Name T,
  --The tyvar tau to which each dynamic thing in the SCC is mapped.
  hmTaus :: Map Name Name,
  --Local -> tyvar; unused during kind and sv check
  hmLocals :: Map Name T --local -> tyvar; inferred from v = e
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
data HMError = Can'tConstructTheInfiniteType Name T --a ~ T a
             | Can'tUnify T T
             | NonTypeInArrow T T
             --Only an error after inference:
             | KindVarUnbound Name
             --The result of looking up the tau of a non-scc name
             | TauOfNonSCCMember Name
             | MalformedPatternInFunctionParam E
             | ScopeErrorInTypeOf Name
             | NonFunctionMustBeMonomorphic Name T
             | RigidUnificationError RigidUnificationError
             | InTypeOfFun Pat S HMError
             | InInferBlock T [S] HMError
             | InTypeOf E HMError
             | InUnify (T,T) HMError
             --switching to tuple for easier error reading
             | KindHasNoDefault Name
             | CompositeKindCannotBeDefaulted T
             | FunctionPatShadowsStaticNames (Set Name)
             | Can'tAssignStaticThing Name
             | NoSuchField Name
             | NoSuchConstructor Name
             | PConArgsArityMismatch Name [Pat] Int
             | NoSuchFieldInCon Name Name --field, con
             | HMCompilerError String --if this is thrown it's the compiler's
             --fault, not the programmers. Used for better error reporting.
             | HMAnnotPath String HMError
             --A single constructor for debug tracing
             | InvalidAmpersandExpr E
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
                   | InCheckSignature Name (HMError,HMS)
                   | NonexistentKindDefaulted Name T
                   | KindDefaultsToPolymorphicType Name T
                   | KindDefaultMismatch Name HMError
                   | InCheckConTag Name HMError
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
data ConstructorError = InNthArgument Int T ConstructorArgumentError
  deriving (Eq,Ord,Read,Show)
data ConstructorArgumentError = TyVarsNotInScope (Set Name)
                              | HMErrorInCon (HMError,HMS)
  deriving (Eq,Ord,Read,Show)
tcModule :: Module -> Either TCModuleError Module
tcModule m = do
  tcTysigs m
  tcKindsigs m
  tcDefaults m
  tcDatatypes m
  tcGlobals m
  complainIf (S.member "Kind" $ S.union (M.keysSet $ kindsigs m)
               (kinds m))
    KindMayHaveNoKind
  --Before we infer types, we add constructor and field types to tysigs
  --We also modify the signatures of globals with signatures here.
  let m' = addConsAndFieldsToTySigs m
  m'' <- inferTypes m'
  return m''

--Failure modes for default k = t:
--k is not in sorts (TODO rename to kinds?)
--t is polymorphic
--t is not of kind k
tcDefaults :: Module -> Either TCModuleError ()
tcDefaults m = do
  let ds = M.toList $ defaults m
  mapM_ (\(k,t) -> do
            complainIf (not $ S.member k $ kinds m)
              $ NonexistentKindDefaulted k t
            complainIf (polymorphic t)
              $ KindDefaultsToPolymorphicType k t
            let hmr = newHMR{hmKindSigs = kindsigs m,
                             hmSorts = kinds m
                            }
            case runHM (go k t) hmr newHMS of
              (Left hme, s) -> throwError $ KindDefaultMismatch k hme
              _ -> return ()) ds
    where go k t = do
            k' <- kindOf t
            unifyK (TyCon k) k'

--Just checks each global without an initializer has a signature
tcGlobals :: Module -> Either TCModuleError ()
tcGlobals m = do
  let offenders = do
        (g,(r,me)) <- M.toList $ globals m
        if (me == Nothing) && not (M.member g $ tysigs m)
          then return g
          else []
  complainIf (not $ null offenders)
    $ TysigsMandatoryForUnitializedGs offenders

--For each TyCon params, bind the params to the kinds given by TyCon's kind
--then unify each arg's kind with Type.
--data Con a = Con b is an error; unification may not add new tyvars to scope
--To maintain the invariant that unify doesn't expect any tyvars not bound
--to a kind, check for out of scope vars first.
--As before, check for no unbound kind vars with allKindsBound.

--Change: reuse the same code but extract tycon, params, [(con,ts)] from
--dtsInfo. condecls is changed from [(con,Either ts nmts)] to [(con,ts)]
--TODO check con tag as well!
tcDatatypes :: Module -> Either TCModuleError ()
tcDatatypes m = do
  --Adjustment: dts remains mostly the same, we just compute it
  --differently.
  let dtsi = dtsInfo m
      dts = map (\(tycon,dti) ->
                      (tycon,(dtParams dti,
                               map (\con ->
                                      let ci = conInfo dtsi ! con
                                      in (con, map snd $ conFields ci)
                                   ) $ dtCanonicalCons dti))
                  )
            $ M.toList $ datatypes dtsi
      hmr = newHMR{hmKindSigs = kindsigs m,
                   hmSorts = kinds m
                  }
  mapM_ (\(tycon,(params,condecls)) -> (do
           --Note duplicate params have been ruled out earlier
           let k = kindsigs m ! tycon
           --FIKS also guarantees tycon is in kindsigs, its arity matches
           --params and the return kind is Type
           let (kargs,_) = splitTyFun k
               param2kind = M.fromList $ zip params kargs
               paramSet = S.fromList params
               hms = newHMS{hmTyVars = param2kind}
           mapM_ (\(con, ts) -> (
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
                         ? InNthArgument nth t) $ zip [1..] ts)
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
            | S.member nm (kinds m) -> return ()
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
                         _ | S.member nm $ M.keysSet $ globals m -> do
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
                                 hmSorts = kinds m
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
              hmDTsInfo = newDTsInfo,
              hmKindSigs = e,
              hmSorts = S.empty,
              hmDefaults = e,
              hmTaus = e,
              hmLocals = e
             }
  where e :: Map k v
        e = M.empty
        newDTsInfo =
          DTsInfo {
          datatypes = e,
          conInfo = e,
          fieldInfo = e
                  }
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
  where go e = withError (InTypeOf e) $ (\case
          EInteger n -> return (EInteger n, UInt 32)
          -- &e desugaring
          Var "addressOf" :$ e -> typeOfAmpersand e
          f :$ x -> do
            (f',tf) <- go f
            (x',tx) <- go x
            b <- newTyVar
            --dbgf <- zonk tf
            --dbgx <- zonk tx
            --unsafePrint $ "(tf,tx): " ++ show (dbgf,dbgx)
            --unify ("Unit" :-> "Unit") ("Unit" :-> "Unit")
            --unsafePrint "Could do that at least"
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
            (p',tp) <- typeOfPat p
            (e',te) <- go e
            unify tp te
            return (p' := e', te)
          EArray Nothing es -> do
            a <- newTyVar
            e'ts <- mapM go es
            let e's = map fst e'ts
                ts = map snd e'ts
                len = length es
            mapM_ (unify a) ts
            t <- zonk a
            return (EArray (Just t) e's, Array (TyNat $ fromIntegral len) a)
          TyApp e t -> error "Compiler error: TyApp should not appear yet!"
          --I don't currently have syntactic support for ecase...
          CaseE e pates -> error "todo"
          --Issue: I need to save the type params for the op, but their
          --number depends on the op (e.g. shL has 4, bwAnd has 1).
          --I also don't want to repeat the opfun lookup.
          --Solution: I'll cache the inferred opfun in a Maybe E
          OPAssign Nothing p op e -> do
            (p',tp) <- typeOfPat p
            (e',te) <- go e
            let opfun = Var $ op2fun op
            (opfun',top) <- typeOf opfun
            let Pair a b :-> c = top
            unify tp a
            unify te b
            unify tp c -- p op= e returns the same type as p...
            c' <- zonk c
            --opfun' will get zonked eventually... 
            return (OPAssign (Just opfun') p' op e', c')
          --p++ uses the inc function which supports both Ptr r a and Int s l.
          --inc : a -> a
          PPPre p -> do
            (p',a) <- typeOfPat p
            return (PPPre p',a)
          PPPost p -> do
            (p',a) <- typeOfPat p
            return (PPPost p',a)
          -- (--) uses dec : a -> a 
          MMPre p -> do
            (p',a) <- typeOfPat p
            return (MMPre p',a)
          MMPost p -> do
            (p',a) <- typeOfPat p
            return (MMPost p',a)
          --The same logic as in PCon: quantify con type, extract its field
          --types, unify with field es.
          ConRecord con Nothing fieldes -> do
            tysigs <- asks hmTySigs
            scheme <- case M.lookup con tysigs of
                        Nothing -> throwError $ NoSuchConstructor con
                        Just t -> return t
            (vars,tcon) <- quantify scheme
            fielde'ts <- forM fieldes (\(field,e) -> do
                                          (e',t) <- go e
                                          return ((field,e'),t))
            let fielde's = map fst fielde'ts
            fields <- fieldsCon con
            let (rhsT,f2t) = assocFieldsWithTs tcon fields
            forM fielde'ts (\((field,_),t) ->
                              case M.lookup field f2t of
                                Nothing ->
                                  throwError $ NoSuchFieldInCon field con
                                Just t' -> unify t t')
            rhsT' <- zonk rhsT
            params <- mapM (zonk . TyVar) vars
            return (ConRecord con (Just params) fielde's, rhsT')
          Dot e Nothing field -> do
            tysigs <- asks hmTySigs
            fieldt <- case M.lookup ('.':field) tysigs of
                        Nothing -> throwError $ NoSuchField field
                        Just t -> return t
            (vars,qt) <- quantify fieldt
            let a :-> b = qt
            (e',et) <- go e
            unify a et
            params <- mapM (zonk . TyVar) vars
            b' <- zonk b
            return (Dot e' (Just params) field, b')
          --Now for the tricky bit...
          --If _, return _ @ a; it's the only polymorphic non-function.
          --If in tysigs, quantify and return that
          --If in locals, return the associated tyvar (zonked)
          --If in SCC, return associated tyvar (zonked)
          --Otherwise, fail with scope error
          Var nm -> do
            hmr <- ask
            case () of
              {-
              --Now deprecated because Pats are once again separate from E.
              _ | nm == "_" -> do
                    v <- newTyVar
                    k <- kindOf v
                    unifyK k "Type"
                    return (TyApp "_" [v], v)
-}
              _ | Just scheme <- M.lookup nm $ hmTySigs hmr -> do
                  (vars,t) <- quantify scheme
                  return (TyApp nm $ map TyVar vars, t)
                | Just t <- M.lookup nm $ hmLocals hmr -> do
                  t' <- zonk t
                  return (TypedVar (Just t') nm, t')
                | Just v <- M.lookup nm $ hmTaus hmr -> do
                    t <- zonk $ TyVar v
                    return (TypedVar (Just t) nm, t)
                | let -> throwError $ ScopeErrorInTypeOf nm) e
--e ::= *E | e.field | e!ix
--Hacky approach: first get a from typeOf e, then get the type of the
--pointer to get the r. Result: Ptr r a
typeOfAmpersand :: E -> HM (E,T)
typeOfAmpersand e =
  case disassembleAmpersandExpr e of
    Nothing -> throwError $ InvalidAmpersandExpr e
    Just ptr -> do
      (e',a) <- typeOf e
      (_,ptrt) <- typeOf ptr
      let Ptr r _ = ptrt --This can't fail after typeOf e passes... right?
      a' <- zonk a
      r' <- zonk r
      return (TyApp "addressOf" [a',r'] :$ e', Ptr r' a')
--Gets the pointer in the expr if it's a valid ampersand expr (pre-HM)
disassembleAmpersandExpr :: E -> Maybe E
disassembleAmpersandExpr = go
  where go = \case
          Dot e Nothing _field -> go e
          Var "indexArray" :$ tup
            | Just [arr,ix] <- unTupleE tup ->
              go arr
          Var "deref" :$ ptr -> return ptr
          _ -> Nothing
  
                         
--Convert _ to a new local here; that lets me avoid tagging _ with type.
typeOfPat :: Pat -> HM (Pat,T)
typeOfPat = go
  where
    go = \case
      --Issue: now there'll be $wild<n> names which aren't declared anywhere.
      PWild -> do
        wild <- newVarNamed "wild"
        t <- newTyVar
        k <- kindOf t
        unifyK k "Type"
        return (TypedPVar (Just t) wild, t)
      --If the name is a function or global (in hmTySigs or hmTaus), fail -
      --f and &g can't be assigned.
      --If it's a local, look it up in hmLocals and zonk the type.
      PVar v -> do
        hmr <- ask
        case () of
          _ | S.member v $ S.union (M.keysSet $ hmTySigs hmr)
              (M.keysSet $ hmTaus hmr) ->
              throwError $ Can'tAssignStaticThing v
            | Just t <- M.lookup v $ hmLocals hmr -> do
                  t' <- zonk t
                  return (TypedPVar (Just t') v, t')
            --Add a different error type for pattern? Or InTypeOfPat...
            | let -> throwError $ ScopeErrorInTypeOf v
      Deref Nothing e -> do
        (e',t) <- typeOf e
        r <- newTyVar
        a <- newTyVar
        --Do I need to unifyK here?
        unify t (Ptr r a)
        r' <- zonk r
        a' <- zonk a
        return (Deref (Just [r',a']) e',a')
      --PDot: look up .field : a -> b in tysigs, treat as application.
      --Using FIKS to put field types in tysigs avoids the need to modify HMR,
      --but having a separate map for fields is cleaner...
      PDot Nothing pstruct field -> do
        tysigs <- asks hmTySigs
        case M.lookup ('.':field) tysigs of
          Nothing -> throwError $ NoSuchField field
          Just scheme -> do
            (vars,tfield) <- quantify scheme
            let a :-> b = tfield
            (p',tstruct) <- go pstruct
            unify tstruct a
            b' <- zonk b
            return (PDot (Just $ map TyVar vars) p' field, b')
      --Array len a ! Short : a
      PBang Nothing parr eix -> do
        (parr',tarr) <- go parr
        (eix',tix) <- typeOf eix
        unify tix (UInt 16)
        len <- newTyVar
        a <- newTyVar
        unify tarr (Array len a)
        len' <- zonk len
        a' <- zonk a
        return (PBang (Just [len',a']) parr' eix', a')
        --PConArgs: look up con type, treat as application
      PConArgs con Nothing ps -> do
        (vars,conT) <- pconPrefix con
        p'ts <- mapM go ps
        let p's = map fst p'ts
            ts = map snd p'ts
        --The number of ps must match the number of fields of
        --the constructor. t is guaranteed to have an arity >= #fields.
        conArity <- length <$> fieldsCon con
        complainIf (length p'ts /= conArity)
          $ PConArgsArityMismatch con ps conArity
        rhsT <- unifyConArgs conT ts
        typarams <- mapM (zonk . TyVar) vars
        return (PConArgs con (Just typarams) p's, rhsT)
      --PCon: look up field types, unify
      PCon con Nothing fieldps -> do
        (vars,conT) <- pconPrefix con
        fs <- fieldsCon con
        --Each field in fs must be associated with an argument type in conT
        let (rhsT,f2t) = assocFieldsWithTs conT fs
        fieldps' <- forM fieldps (\(field,p) ->
                                    case M.lookup field f2t of
                                      Nothing -> throwError $
                                        NoSuchFieldInCon field con
                                      Just t -> do
                                        (p',pt) <- go p
                                        unify pt t
                                        return (field,p'))
        typarams <- mapM (zonk . TyVar) vars
        return (PCon con (Just typarams) fieldps', rhsT)
                                     
    --rhsT <- unifyConArgs conT ts
    unifyConArgs rhsT [] = return rhsT
    unifyConArgs (argT :-> conT') (t:ts) = do
      unify t argT
      unifyConArgs conT' ts
    --The shared prefix of PConArgs and PCon(record)
    pconPrefix con = do
      tysigs <- asks hmTySigs
      case M.lookup con tysigs of
        Nothing -> throwError $ NoSuchConstructor con
        Just scheme ->
          quantify scheme
assocFieldsWithTs rhsT [] = (rhsT,M.empty)
assocFieldsWithTs (argT :-> conT') (f:fs) =
  let (rhsT,m) = assocFieldsWithTs conT' fs
  in (rhsT, M.insert f argT m)
--Get the fields of a Con; precond: the Con exists
--Also used in typeOf
fieldsCon :: Name -> HM [Name]
fieldsCon con = do
  dtsi <- asks hmDTsInfo
  let ci = conInfo dtsi ! con
  return $ map fst $ conFields ci
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
  {-
  --(->) is always Type -> Type -> Type in this context
  --It's also only ever fully applied.
  a :-> b -> do
    ka <- kindOf a
    unifyK ka "Type"
    kb <- kindOf b
    unifyK kb "Type"
    return "Type"
  -}
  --f x := return 3 fails because kindOf encounters (->) Word... but why!?
  --Hotfix: give (->) a kind
  TyCon "->" -> return $ "Type" :-> "Type" :-> "Type"
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
    a2kv <- gets hmTyVars
    kv <- case M.lookup a a2kv of
               Just kv -> return kv
               Nothing ->
                 throwError $ HMCompilerError $
                 "Tyvar "++a++" unexpectedly lacks kind var; " ++
                 "hmTyVars: " ++ show a2kv
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
  withError (InUnify (t1',t2')) $ do
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
        unify tx ty
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
  m' <- go m nmss
  --Now that everything without an initial tysig has been inferred, we must
  -- *check* the types of funs, stats and globs which had tysigs from the start.
  --That involves updating their definitions to add TyApps.
  --Not doing so doesn't explain why "id x := x" infers to a, but
  --"f x := return g x; g x := return f x" types correctly...
  let sigfuns = withSigs defuns
      sigglobs = withSigs globals
  --normal defs and classes have a different shape, so they need different
  --control flow... I'll check them separately.
  let isClass = \case
        Left _ -> False
        Right _ -> True 
  fun2def <- checkWSigs m' goF defuns $ filter (\f ->
                                                  case M.lookup f (defuns m) of
                                                    Just (Left _) -> True
                                                    _ -> False)
             sigfuns
  let classes = M.map (\(Right s) -> s) $
                M.filter isClass $ defuns m'
  fun2class <- M.map Right <$> checkClasses m' classes
  glob2e <- checkWSigs m' goG globals sigglobs
  --TODO add DT tag inference here
  dts <- inferConTags m'
  return m'{defuns = M.unions [fun2class,fun2def,defuns m'],
            globals = M.union glob2e $ globals m',
            dtsInfo = dts
           }
  where go m = \case
          [] -> return m
          nms:nmss -> do
            m' <- inferSCC nms m ? InInferSCC nms
            go m' nmss
        withSigs f = S.toList $ S.intersection (M.keysSet $ f m) $
                     M.keysSet $ tysigs m
        --Is there any reason I can't use m' instead f m in checkWSigs..?
        checkWSigs :: (Show def, Data def) =>
                      Module ->
                      (T -> def -> HM def) ->
                      (Module -> Map Name def) ->
                      [Name] ->
                      Either TCModuleError (Map Name def)
        checkWSigs m' handler field nms =
          M.fromList <$> mapM (\nm -> do
                                  let def = field m ! nm
                                      sig = tysigs m ! nm
                                  case runHM (handler sig def)
                                       (hmr m') newHMS
                                    of
                                    (Left err, s) -> Left $
                                      InCheckSignature nm (err,s)
                                    (Right def', _) ->
                                      return (nm,def')) nms
        hmr m' = HMR{hmTySigs = tysigs m',
                     hmDTsInfo = dtsInfo m,
                  hmKindSigs = kindsigs m, --kinds and sorts not changed
                  hmSorts = kinds m,
                  hmDefaults = defaults m,
                  hmTaus = M.empty, --They'll remain empty
                  hmLocals = M.empty
                 }
        --Can't use goSig with its current definition... multiple instances
        --need to be checked for <= generality.
        goF t (Left pats) = Left <$> goSig (typeOfFun m) t pats
        --goS = goSig typeOf
        goG = goSig $ \(r,me) ->
                        case me of
                          Just e -> do
                            (e',t) <- typeOf e
                            return ((r,Just e'),t)
                          Nothing -> return ((r,Nothing),TyVar "whatever")

--Given a TC'd module where every global and function already has a tysig:
--for each datatype DT params:
-- t<params> = its tag type
-- for each constructor Con:
--  e = its tag expr
--  e',t' <- typeOf e
--  e'' <- compare and adapt to rigid signature t<params>
--   as with signed functions, after this e''s tyvars will be in params
--  update tag to e''
inferConTags :: Module -> Either TCModuleError (DTsInfo E)
inferConTags m = do
  let dtsi = dtsInfo m
      dts = M.toList $ datatypes dtsi
  --Result: a list of maps Con => ConInfo E
  csi's <- forM dts (\(tycon,dti) -> do
                        let DTInfo {dtParams = params,
                                    dtTagType = sig,
                                    dtCanonicalCons = cons
                                   } = dti
                            csi = conInfo dtsi
                        --Result: a map Con => ConInfo E
                        csi' <- forM cons (\con -> do
                                              let Just ci = M.lookup con csi
                                                  e = conTag ci
                                              e' <- case runHM (go sig e)
                                                         hmr newHMS of
                                                (Left hme,_) ->
                                                  Left $ InCheckConTag con hme
                                                (Right a, _) -> return a
                                              return (con,ci{conTag = e'})
                                          )
                        return $ M.fromList csi'
                    )
  --M.unions that = the new conInfo
  return dtsi{conInfo = M.unions csi's}
    where hmr = HMR{
            hmTySigs = tysigs m,
            hmDTsInfo = dtsInfo m,
            hmKindSigs = kindsigs m, 
            hmSorts = kinds m,
            hmDefaults = defaults m,
            hmTaus = M.empty, --They'll remain empty
            hmLocals = M.empty
            }
          go = goSig typeOf
--Moving to top level to be able to use it in checkClasses as well...
goSig :: (Show def,Data def) => (def -> HM (def,T)) -> T -> def ->
          HM def
goSig handler sig def = do
          (def',t) <- handler def
          --All kinds must be bound at this point
          allKindsBound
          --The def may be more general than the sig, but not less general...
          --First obtain a mapping from tyvars in the inferred type to T's in
          --the scheme; scheme vars are rigid, so if they're bound that's an
          --error.
          --Apply the mapping to each type present in it; vars not present
          --are unbound by t and should be defaulted instead.
          t' <- zonk t --Just in case
          {-
          let ei_err_inf2sig = execStateT (unifyRigid sig t) M.empty
          inf2sig <- case ei_err_inf2sig of
                       Left rue -> throwError $ RigidUnificationError rue
                       Right inf2sig -> return inf2sig
-}
          inf2sig <- matchWithSig t' sig
          rigidizeAndDefault inf2sig def'
--Attempts to match t with the rigid type sig; t must be at least as general
--as sig. Returns inf2sig (t var -> sig type), which is passed to
--rigidizeAndDefault.
matchWithSig :: T -> T -> HM (Map Name T)
matchWithSig t sig = do
  let e =  execStateT (unifyRigid sig t) M.empty
  case e of
    Left rue -> throwError $ RigidUnificationError rue
    Right inf2sig -> return inf2sig
--Have the instance types been kind checked yet?
--For each (f,set), look up f : scheme;
--for each (t,p,s) in set:
-- check t is an instance of scheme
-- check p,s vs t, unify and zonk
checkClasses :: Module -> Map Name (Set (T,Pat,S)) ->
  Either TCModuleError (Map Name (Set (T,Pat,S)))
checkClasses m classes =
  M.fromList <$> (forM (M.toList classes) $
                  \(f,set) -> do
                    let scheme = tysigs m ! f
                    set' <- S.fromList <$>
                       (forM (S.toList set) $ \(t,p,s) -> do
                           (p',s') <- checkSig m
                             (\t (p,s) -> do
                                 withError (HMAnnotPath $
                                            "matching t w/ sig: " ++ show
                                           (t,scheme)) $
                                   --The scheme must be more general than the
                                   --instance!
                                   matchWithSig scheme t
                                 goSig (typeOfFun m) t (p,s)
                             ) f (p,s) t
                             
                           return (t,p',s')
                       )
                    return (f,set')
                 )

checkSig :: (Show def, Data def) =>
              Module ->
              (T -> def -> HM def) ->
              Name -> def -> T ->
              Either TCModuleError def
checkSig m handler name def sig =
  case runHM (handler sig def) hmr newHMS of
    (Left err, s) -> Left $ InCheckSignature name (err,s)
    (Right def', _) -> return def'
  where
    hmr = HMR{hmTySigs = tysigs m,
              hmDTsInfo = dtsInfo m,
              hmKindSigs = kindsigs m, --kinds and sorts not changed
              hmSorts = kinds m,
              hmDefaults = defaults m,
              hmTaus = M.empty, --They'll remain empty
              hmLocals = M.empty
             }
--Replaces inferred tyvars with the rigid type they're bound to.
--Fix: defaults must be applied on a per-kind basis.
--If non-rigid a :: k where k lacks a default, fail.
--If k is polymorphic, that's a compiler error.
--To look up kinds and defaults, rigidize must be in HM.
rigidizeAndDefault :: (Show a, Data a) => Map Name T -> a -> HM a
rigidizeAndDefault inf2rigid d =
  withError (HMAnnotPath $ "rad: " ++ show d) $ everywhereButStopM isT (mkM $
  \t -> withError (HMAnnotPath $ "inrad: " ++ show t) $
        zonk t >>=
        rigidizeAndDefaultType inf2rigid) d
--Invariant: after zonking, all tyvars in the type are unbound.
--Either they're in inf2rigid or not.
rigidizeAndDefaultType :: Map Name T -> T -> HM T
rigidizeAndDefaultType inf2rigid t =
  withError (HMAnnotPath $ "radt: " ++ show (inf2rigid,t)) $ go t
  where
    go = \case
      tf :$$ tx -> (:$$) <$> go tf <*> go tx
      TyVar a | Just t <- M.lookup a inf2rigid -> return t
              | otherwise -> defaultFreeTyVar a
      t -> return t

  {-everywhereM $ mkM $
  \case TyVar a | Just t <- M.lookup a inf2rigid -> return t
                | otherwise -> defaultFreeTyVar a
        t -> return t-}

--Attempts to find the default instance for a tyvar that's not bound by the
--inferred signature.
--Also used in default logic for defs without signatures.
defaultFreeTyVar :: Name -> HM T
defaultFreeTyVar a = do
  k <- withError (HMAnnotPath "defaultFreeTyVar kindOf") $ kindOf (TyVar a)
  ds <- asks hmDefaults
  case k of
    TyCon kcon ->
      case M.lookup kcon ds of
        Just dflt -> return dflt
        Nothing -> throwError $ KindHasNoDefault kcon
    --Can occur if tyvar = m in m a, for example
    _ -> throwError $ CompositeKindCannotBeDefaulted k
--A single inferred var mapping to two different rigid vars is also an error.
--Example: a -> a is less general than a -> b.
type UnifyRigid = StateT (Map Name T) (Either RigidUnificationError)
unifyRigid :: T -> T -> UnifyRigid ()
unifyRigid = go
  where go rt (TyVar a) = bindRigid a rt
        go (TyVar rv) t = throwError $ RigidVarBoundToNonVar rv t
        go (rf :$$ rx) (sf :$$ sx) = go rf sf >> go rx sx
        go rt st = complainIf (rt /= st)
          $ RigidUnificationFailure rt st
        bindRigid :: Name -> T -> UnifyRigid ()
        bindRigid a rt = do
          mrt' <- gets $ M.lookup a
          case mrt' of
            Nothing -> modify $ M.insert a rt
            Just rt' -> complainIf (rt /= rt')
                        $ InferredVarMapsToTwoRigidTypes a (rt,rt')
data RigidUnificationError = RigidVarBoundToNonVar Name T
                           | InferredVarMapsToTwoRigidTypes Name (T,T)
                           | RigidUnificationFailure T T
  deriving (Eq,Ord,Read,Show)
                                        
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
    (Right (sigs,funs,globs), _) ->
      return m{tysigs = M.union sigs $ tysigs m,
               defuns = M.union (M.map Left funs) $ defuns m,
               globals = M.union globs $ globals m
              }
  where hmr = HMR{hmTySigs = tysigs m,
                  hmDTsInfo = dtsInfo m,
                  hmKindSigs = kindsigs m,
                  hmSorts = kinds m,
                  hmDefaults = defaults m,
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
          --unsafePrint "Got here A"
          withReaderT (\hmr->hmr{hmTaus=nm2tau}) $ do
            --For each nm in nms, infer type to get an updated definition and
            --unify the type with tau
            (funs,globs) <- inferDefs m nms
            --unsafePrint "Got here B"
            --Zonk taus; if any static or global is polymorphic fail
            --return nm->zonked and prettified tau and updated defs
            nm2uglySig <- M.fromList <$>
                      mapM (\nm -> do
                               t <- tauOf nm >>= zonk
                               complainIf ((S.member nm $
                                            M.keysSet $ globals m) &&
                                           polymorphic t)
                                 $ NonFunctionMustBeMonomorphic nm t
                               return (nm,t)) nms
            let nm2sig = M.map prettifyType nm2uglySig
            allKindsBound
            --zonk all tyapps in the defs
            (funs',globs') <- everywhereM (mkM zonk) (funs,globs)
            --Default unbound tyvars *on a per-function basis*
            funs'' <- applyDefaults funs' nm2uglySig
            --stats and globs are monomorphic, so *all* tyvars must be
            --defaulted. However, it's simpler to use the same function for
            --that.
            --stats'' <- applyDefaults stats' nm2sig
            globs'' <- applyDefaults globs' nm2uglySig
            --Fail if any kind var is unbound
            return (nm2sig,funs'',globs'')

--Need to apply rigidizeAndDefault here; the rigid signature is the inferred
--one (so the inf2rigid map is just an identity map on all the vars in the
--signature).
{-
          --The def may be more general than the sig, but not less general...
          --First obtain a mapping from tyvars in the inferred type to T's in
          --the scheme; scheme vars are rigid, so if they're bound that's an
          --error.
          --Apply the mapping to each type present in it; vars not present
          --are unbound by t and should be defaulted instead.
          t' <- zonk t --Just in case
          let ei_err_inf2sig = execStateT (unifyRigid sig t) M.empty
          inf2sig <- case ei_err_inf2sig of
                       Left rue -> throwError $ RigidUnificationError rue
                       Right inf2sig -> return inf2sig
          rigidizeAndDefault inf2sig def'
-}
            

--Ah, I've duplicated defaulting here...
--I'll also prettify the types
applyDefaults :: (Show a, Data a) => Map Name a -> Map Name T -> HM (Map Name a)
applyDefaults nm2def nm2t = do
  let nmdefs = M.toList nm2def
  M.fromList <$> (mapM (\(nm,def) ->
                        let scheme = nm2t ! nm
                            prettyMap = M.fromList $
                                        zip (tyVarsList scheme) pretties
                            --Use rigidizeAndApplyDefaults here instead?
                        in do
                          def' <- everywhereM (mkM $ \case
                            TyVar a
                              | Just p <- M.lookup a prettyMap ->
                                return $ TyVar p
                              | let -> defaultFreeTyVar a
                            t -> return t) def
                          return (nm,def')
                       )
    nmdefs)


{-
defaultUnboundTyVars :: HM ()
defaultUnboundTyVars = do
  tyvs <- M.keys <$> gets hmTyVars
  mapM_ (\tyv -> do
            mt <- M.lookup tyv <$> gets hmTyMap
            case mt of
              Nothing -> unify (TyVar tyv) (UInt 256)
              Just _ -> return ()) tyvs
-}

--Returns updated definitions for functions, statics and globals;
--their type is returned by unifying it with tau
inferDefs :: Module -> [Name] -> HM (Map Name (Pat,S),
                                     Map Name (Region, Maybe E))
inferDefs m = go
  where go = \case
          [] -> return (M.empty,M.empty)
          nm:nms -> do
            (funs,globs) <- go nms
            case () of
              --Note every class fun has a signature, so we can be certain
              --it's a Left pats.
              _ | Just (Left pats) <- M.lookup nm $ defuns m -> do
                    --unsafePrint "Got here A2"
                    (pats',t) <- typeOfFun m pats
                    --unsafePrint "Got here B2"
                    tauOf nm >>= unify t
                    return (M.insert nm pats' funs,globs)
                    {-
                | Just e <- M.lookup nm $ static m -> do
                    (e',t) <-  typeOf e
                    unify t <$> tauOf nm
                    return (funs,M.insert nm e' stats, globs)
-}
                | Just (r,Just e) <- M.lookup nm $ globals m -> do
                  (e',t) <- typeOf e
                  --After desugaring g => *g, every g is in fact a pointer!
                  tauOf nm >>= unify (Ptr (region2T r) t)
                  return (funs,M.insert nm (r,Just e') globs)
                | otherwise -> error "This should never happen"

tauOf :: Name -> HM T
tauOf nm = do
  nm2v <- asks hmTaus
  case M.lookup nm nm2v of
    Just v -> return $ TyVar v
    Nothing -> throwError $ TauOfNonSCCMember nm
--Need to declare args as locals...
--Source of confusion: I had a type Pat = E before.
--p ::= _, x (now only local), *e, p.f, p!e (new), Con ps, Con {field: p}.
--The latter can't be desugared away yet because E has no lets and field
--order determines eval order of Es in the pats.
typeOfFun :: Module -> (Pat,S) -> HM ((Pat,S),T)
typeOfFun m (pat,s) =
  withError (InTypeOfFun pat s) $
  declareArgsAsLocals m pat $ do
  b <- newTyVar --the return type
  kindOf b >>= unifyK "Type"
  k <- kindOf b
  --unsafePrint $ "k: " ++ show k
  (pat',a) <- typeOfPat pat
  ka <- kindOf b
  --unsafePrint $ "ka: " ++ show k
  kindOf a >>= unifyK "Type"
  --unsafePrint $ "Got here C"
  s' <- inferS b s
  --unsafePrint $ "s': " ++ show s'
  return ((pat',s'), a :-> b)
declareArgsAsLocals :: Module -> Pat -> HM a -> HM a
declareArgsAsLocals m pat hm = do
  let vsSet = freeVarsPat pat
  let conflict = S.intersection vsSet staticThings
  complainIf (not $ S.null conflict)
    $ FunctionPatShadowsStaticNames conflict
  let vs = S.toList vsSet
  tyvs <- mapM newTyVarNamed vs
  mapM ((>>= unifyK "Type") . kindOf) tyvs
  let v2tyv = M.fromList $ zip vs tyvs
  withReaderT (\hmr->hmr{hmLocals = v2tyv}) hm
  where
    --go :: Pat -> HM (Set Name)
    --go = error "todo"
    {-
      \case
      EInteger _ -> return S.empty
      Var "_" -> return S.empty
      Var "deref" :$ _e -> return S.empty
      Var "index" :$ _arr :$ _ix -> return S.empty
      Var nm -> return $ if S.member nm staticThings
                         then S.empty
                         else S.singleton nm
      f :$ x -> S.union <$> go f <*> go x
      p ::: t -> go p
      EArray ps -> S.unions <$> mapM go ps
      p -> throwError $ MalformedPatternInFunctionParam p
-}
    staticThings = S.unions [
      ks defuns,
      ks globals
      ]
    ks f = M.keysSet $ f m


--An S can't be inferred by itself because var declaration modifies the locals
--map via withReaderT.
inferS :: T -> S -> HM S
inferS ret s = head <$> inferBlock ret [s]
inferBlock :: T -> [S] -> HM [S]
inferBlock ret ss =
  withError (InInferBlock ret ss) $ inferBlock' ret ss
inferBlock' :: T -> [S] -> HM [S]
inferBlock' ret ss =
   (\case
       [] -> return []
       s:ss -> case s of
                 Declare ves -> withDeclares ves $ inferBlock' ret ss
                 _ -> (:) <$> go s <*> inferBlock' ret ss) ss
  --go handles all the cases but declare since they don't modify scope
  where go = \case
          SE e -> SE <$> fst <$> typeOf e
          Return e -> do
            --unsafePrint "Typing return value..."
            (e',t) <- typeOf e
            --unsafePrint $ "(e',t): " ++ show (e',t)
            unify ret t
            return $ Return e'
          While e s -> While <$> (fst <$> typeOf e) <*> go s
          Case e patss -> do
            (e',t) <- typeOf e
            patsts <- mapM (\(pat,s) -> do
                             (pat',t) <- typeOfPat pat
                             s' <- go s
                             return ((pat',s'),t)) patss
            mapM_ (unify t . snd) patsts
            return $ Case e' $ map fst patsts
          Block ss -> Block <$> inferBlock' ret ss
          Break -> return Break
          Continue -> return Continue
--var x = a, y = b... is sugar for var x = a; var y = b...
--The new local name validity check can be deferred until later...
--A name is invalid if it's one of the statically defined lowercase things:
--a function, static or global
--If a local is redeclared it's shadowed
withDeclares :: [(Name,E)] -> HM [S] -> HM [S]
withDeclares [] hm = hm
withDeclares ((v,e):ves) hm = do
  (e',t) <- typeOf e
  (Declare [(v,e')] :) <$> withReaderT
    (\hmr->hmr{hmLocals=M.insert v t $ hmLocals hmr}) (withDeclares ves hm)
--Assigns a pretty tyvar from a,b..z, a1,b1..z1 for each tyvar in order of
--occurrence.
prettifyType :: T -> T
prettifyType t =
  let vs = tyVarsList t
      v2p = M.fromList $ zip vs pretties
  in substTyVarNames v2p t
--Moved out of the where because it's also used in applyDefaults
pretties :: [Name]
pretties = [[c] | c <- ['a'..'z']] ++
           (do n <- [1..]
               c <- ['a'..'z']
               return $ c : show n
           )
--TODO dedup with Mono.Mono.instT
substTyVarNames :: Map Name Name -> T -> T
substTyVarNames = substTyVars . M.map TyVar
substTyVars :: Map Name T -> T -> T
substTyVars v2t = everywhere (mkT $ \case TyVar v
                                            | Just t <- M.lookup v v2t -> t
                                          t -> t)

--Gathers all mentioned tyvars and returns them in order of first mention
--TODO dedup with Typecheck.Tysyn.TyVars and put in AST.Util
tyVarsList :: T -> [Name]
tyVarsList = fst . tyVarsListSet
tyVarsListSet :: T -> ([Name],Set Name)
tyVarsListSet = everything (\(nms1,snms1) (nms2,snms2) ->
                              (nms1 ++ filter (not . flip S.member snms1) nms2,
                               S.union snms1 snms2)) $ mkQ ([],S.empty) $
                \case TyVar nm -> ([nm],S.singleton nm)
                      _ -> ([],S.empty)
