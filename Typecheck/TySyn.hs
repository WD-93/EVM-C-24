{-# LANGUAGE LambdaCase #-}
module TypeCheck.TySyn where

--The module where the tysyn substitution phase of typechecking is defined.

import Util ((?),complainIf,unsafePrint)

import AST.DTs

import Data.Generics
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Arrow ((***))

data TySynError = TyConsNotInScope (Set Name)
                | TyVarsNotInScope (Set Name)
                | UnderappliedTySyn Name
                | TySynCycle [Name] --ex: type A = B; type B = A
                --Desugar catches this error:
                -- | TySynsShadowPrimTySyns (Set Name)
                | DuplicateTySynParams --need to put it somewhere...
                | In String Name TySynError
                --For location reporting:
                -- | InTySyn Name TySynError
                -- | InDefun Name TySynError
                -- | InStatic Name TySynError
                
  deriving (Eq,Ord,Read,Show)

--Tysyns are not kind checked; that allows them to be kind-polymorphic.
substTySyns :: Module -> Either TySynError Module
substTySyns m = do
  --The set of tycons and tysyn names; used for scope and cycle checking
  let tycons = S.unions [
        M.keysSet $ datatypes m,
        M.keysSet $ kindsigs m,
        sorts m
        ]
      syncons = M.keysSet $ tysyns m
  syns <- handleTySyns tycons syncons $ tysyns m
  let inM f g = inMap f g syns m
  tysigs' <- inM "tysig" tysigs
  kindsigs' <- inM "kindsig" kindsigs
  defuns' <- inM "defun" defuns
  static' <- inM "static" static
  datatypes' <- inM "datatype" datatypes
  constructors' <- inM "constructor" constructors
  fieldTypes' <- inM "field type" fieldTypes
  return m{
    tysigs = tysigs',
    kindsigs = kindsigs',
    defuns = defuns',
    tysyns = syns,
    static = static',
    datatypes = datatypes',
    constructors = constructors',
    fieldTypes = fieldTypes'
    }
  --It might be possible to use everywhereM to just apply the tysyns to
  --everything in one fell swoop... but I don't want to do that since I want
  --to report where any syn error was thrown.
  {-
  
  
  --Globals are a list, not a map...
  globs' <- mapM (\(g,region,t) -> do
                    t' <- genericApplyTySyns syns t ? In "global" g
                    return (g,region,t')) $ globals m
  
-}
inMap :: Data d => String ->
  (Module -> Map Name d) -> Syns ->
  Module -> Either TySynError (Map Name d)
inMap loctype field syns m = M.fromList <$>
        (mapM (\(nm,def) -> do
                  def' <- genericApplyTySyns syns def ? In loctype nm
                  return (nm,def')) $ M.toList $ field m)
  
--The cycle check can be disentangled from tysyn subst in tysyns:
--get syn => syns using SYB, then check for a cycle.

--A simple cycle-finding algorithm
{-
Algo m:
s = {}
for k in m:
 explore [] k
explore stk k:
 if k in s: return ()
 if k in stk: throw stk
 else:
  ks = m[k]
  for k' in ks: explore (k:stk) k'
  s += k
-}
checkForCycle :: Ord k => Map k (Set k) -> Maybe [k]
checkForCycle m = runCheckCycle go m S.empty
  where go = mapM_ (explore []) $ M.keys m
type CheckCycle k = ReaderT (Map k (Set k))
                    (StateT (Set k)
                     (Except [k]))
runCheckCycle :: CheckCycle k () -> Map k (Set k) -> Set k -> Maybe [k]
runCheckCycle cc m s =
  case runExcept $ runStateT (runReaderT cc m) s of
    Left ks -> Just ks
    Right _ -> Nothing
explore :: Ord k => [k] -> k -> CheckCycle k ()
explore stk k = do
  s <- get
  if k `elem` stk
    then throwError stk
    else return ()
  if S.member k s
    then return ()
    else do
    m <- ask
    let ks = m M.! k
    mapM (explore $ k:stk) $ S.toList ks
    modify (S.insert k)

--The scope check can also be; that's less efficient but simpler.
tyVars :: T -> Set Name
tyVars = everything S.union $ mkQ S.empty $ 
         \case
           TyVar nm -> S.singleton nm
           _ -> S.empty
tyCons :: T -> Set Name
tyCons = everything S.union $ mkQ S.empty $
         \case
           TyCon nm -> S.singleton nm
           _ -> S.empty
--allNames :: T -> Set Name
--allNames t = S.union (tyVars t) $ tyCons t

handleTySyns :: Set Name -> Set Name -> Syns -> Either TySynError Syns
handleTySyns tycons syncons syns = do
  scopeCheckTySyns tycons syncons syns
  cycleCheckTySyns syncons syns
  --Finally, recursively substitute all tysyns in tysyn bodies
  normalizeTySyns syns

--Repeated vars in the arg list of a tysyn is an error... I'll report it here
scopeCheckTySyns tycons syncons syns = do
  --Note -> is not in the kind map since it's treated specially (being the
  --only polymorphic tycon)
  let scope = S.insert "->" $ S.union tycons syncons
  mapM_ (\(synnm,(args,body)) ->
            (do let vars = tyVars body
                    argset = S.fromList args
                    vardiff = S.difference vars argset
                complainIf (S.size argset < length args)
                  DuplicateTySynParams
                complainIf (vardiff /= S.empty)
                  $ TyVarsNotInScope vardiff
                let cons = tyCons body
                    condiff = S.difference cons scope
                complainIf (condiff /= S.empty)
                  $ TyConsNotInScope condiff
            ) ? In "tysyn" synnm
        )
    $ M.toList syns

cycleCheckTySyns :: Set Name -> Syns -> Either TySynError ()
cycleCheckTySyns syncons syns = do
  let syn2syns = M.map (\(_,body) ->
                          S.intersection syncons $ tyCons body) syns
  case checkForCycle syn2syns of
    Just syncons -> Left $ TySynCycle syncons
    _ -> return ()

--Recursively apply tysyns; because they're now guaranteed to be acyclic this
--will terminate.
{-
norms = {}
for syncon in syns:
 normalize syncon
normalize syn:
 if syn in norms: return ()
 (args,body) = syns[syn]
 mentioned = tyCons intersection syncons
 normalize each syn in mentioned
 --At this point norms will contain the requisite synonyms
 body' = applyTySyns norms body
 norms[syn] = (args,body')
-}
normalizeTySyns :: Syns -> Either TySynError Syns
normalizeTySyns syns = do
  let synsList = M.keys syns
  runNorm (mapM_ normalizeTySyn synsList) syns M.empty
normalizeTySyn :: Name -> Norm ()
normalizeTySyn syn = do
  norms <- get
  if M.member syn norms
    then return ()
    else do
    unorms <- ask
    --Scope check ensures this won't fail
    let (args,body) = unorms M.! syn
        --Could optimize this to avoid repeated keys...
        mentioned = S.intersection (M.keysSet unorms) $ tyCons body
    mapM_ normalizeTySyn mentioned
    newnorms <- get --contains everything we need
    case applyTySyns newnorms body of
      Left err -> throwError $ In "tysyn" syn err
      Right body' -> modify $ M.insert syn (args,body')
    
--TODO use that combined reader, writer, state, except monad
type Norm = ReaderT Syns --un-normalized syns
                    (StateT Syns --normalized syns
                     (Except TySynError))
runNorm :: Norm a -> Syns -> Syns -> Either TySynError Syns
runNorm norm uns nos =
  snd <$> (runExcept $ runStateT (runReaderT norm uns) nos)

--Subst scheme: collect tyapps into (tf,targs), then recursively subst
--targs.
--If tf is a tysyn, require |targs| >= its arity and apply the subst.
--If it's a tycon or var, check it's in scope and apply it.
--Because tysyns have been normalized, we don't need to repeatedly substitute.
applyTySyns :: Syns -> T -> Either TySynError T
applyTySyns syns t = do
  let (tf,targs1) = rollTyApps t
  targs2 <- mapM (applyTySyns syns) targs1
  case tf of
    TyCon con
      | Just (args,body) <- M.lookup con syns ->
        do let arity = length args
           complainIf (arity > length targs2)
             $ UnderappliedTySyn con
           let prefix = take arity targs2
               suffix = drop arity targs2
               substMap = M.fromList $ zip args prefix
           --Note this algo will be broken if I add rank-2 types that can
           --close variables
           let res = everywhere (mkT $ \case TyVar v -> substMap M.! v
                                             t -> t) body
           return $ unrollTyApps res suffix
    _ -> return $ unrollTyApps tf targs2

--splits f x y .. z into (f,[x,y .. z])
rollTyApps :: T -> (T,[T])
rollTyApps t = (id *** reverse) $ go t
  where go = \case
          tf :$$ tx ->
            let (tf',args) = go tf
            in (tf', tx : args)
          t -> (t,[])
unrollTyApps = foldl (:$$)

--Thank you SYB
genericApplyTySyns :: Data a => Syns -> a -> Either TySynError a
genericApplyTySyns syns = everywhereM (mkM $ applyTySyns syns)
