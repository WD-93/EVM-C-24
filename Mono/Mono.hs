{-# LANGUAGE LambdaCase #-}
module Mono.Mono where

--On the EVM, you can't afford boxing datatypes by default.
--EVMC therefore has a Hindley-Milner type system with template polymorphism,
--in contrast to Haskell's approach of passing boxed class dicts.
--That allows id : a -> a to work for both Word and (Word,Word); separate
--machine code is generated for each instance.
--To achieve that, EVMC modules must first be monomorphized: starting from
--main : () -> (), type annotations containing rigid tyvars are replaced with
--monomorphic types. For each f @ monoTs, a new monomorphic function is
--allocated.
--For class functions, an instance must be selected first.
--This phase also tree-shakes the relevant function instances, globals and
--datatypes.
--Note that globals are already monomorphic... but they must still be explored
--to get the full function instance set.

import AST.DTs
import Util (complainIf,(!))
import Typecheck.HM (tyVarsList)

import Data.Generics
import Control.Monad (forM)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M hiding ((!))

--Algo:
--First look up main;
--unify its type with () -> (), obtaining the params ts to pass to its scheme
--monoFun f monoTs:
--If f@monoTs has not yet been created:
-- Look up f's scheme, replace scheme's vars with monoTs in its body
-- Wherever a f@polyTs is encountered,
--  updTs = update polyTs using the var=>monoT mapping
--  monoFun f updTs
--  replace with f@updTs
-- funs[f@monoTs] = the updated definition
--If Con@monoTs has not yet been explored:
-- Explore from its monomorphized tag.

--When monomorphizing a class function, also need to instantiate.
--That's never relevant to tag expressions, which should be static.
--Instantiating a class function f@monoTs:
--monoF = instantiateT (tysigs[f]) monoTs
--Match monoF vs instance schemes until a match monoTs' is found
--Set polymorphic body to the instance's and instantiate with monoTs'

--There are three dynamic-relevant fields:
--defuns, globals, dtsInfo.
--Root: main
--Funs can mention funs, globals and constructors
--Globals and tag expressions contain static exprs; those may in turn refer
--to all three.

--The only thing mono modifies is the set of functions;
--however, it also prunes the set of relevant globals and constructors.
data MonoS = MonoS {
  --We also cache the monomorphic type signature
  exploredFuns :: Map (Name,[T]) (T,(Pat,S)),
  exploredGlobals :: Set Name,
  --If one constructor is live, all must be (because in the worst case you
  --must do an O(n) scan of arbitrary-valued tags when you case).
  --DT params is live if any of its Cons or fields are (in E or Pat).
  --We also cache the monomorphic tag exprs.
  exploredDTs :: Map (Name,[T]) (Map Name E)
                   }
  deriving (Eq,Ord,Read,Show)
monomorphize :: Module -> Either MonoError MonoS
monomorphize m = runExcept $ flip execStateT s $ flip runReaderT m go
  where s = MonoS M.empty S.empty M.empty
        go :: Mono ()
        go = do
          complainIf (not $ M.member "main" $ defuns m)
            $ NoMainFunction
          let Just tmain = M.lookup "main" $ tysigs m
          params <- case bindT tmain (Unit :-> Unit) of
                      Left bindError ->
                        throwError $ IlltypedMainFunction tmain bindError
                      Right v2t ->
                        let vs = tyVarsList tmain
                            ts = map (v2t !) vs
                        in return ts
          monoFun "main" params

type Mono = ReaderT Module (StateT MonoS (Except MonoError))
data MonoError = InMonoFun (Name,[T]) MonoError
               | InMonoGlobal Name MonoError
               | InMonoDT (Name,[T]) MonoError
               | NoInstanceForClass T [T]
               | NoMainFunction --note a global main triggers this
               | IlltypedMainFunction T BindError
  deriving (Eq,Ord,Read,Show)

monoFun :: Name -> [T] -> Mono ()
monoFun f monoTs = withError (InMonoFun (f,monoTs)) $ do
  mps <- gets (M.lookup (f,monoTs) . exploredFuns)
  case mps of
    Just _ -> return () --already explored
    Nothing -> do
      --Look up tysig, get vars; map them to monoTs and inst sig
      scheme <- (! f) <$> asks tysigs
      let vars = tyVarsList scheme
      --Just in case...
      if length vars /= length monoTs
        then error $ "Compiler error: wrong tyapp arity in monoFun " ++ f
             ++ ": " ++ show (vars,monoTs)
        else return ()
      let v2t = M.fromList $ zip vars monoTs
          Right ft = instT v2t scheme
      --Look up def; note we already know f is a function
      def <- (! f) <$> asks defuns
      --monomorphize the def
      ps <- case def of
              --if class, choose first instance whose sig matches
              --error if none do. Map its tyvars (distinct from those of
              --the class sig) to monomorphic types
                Right tpsset ->
                  let tpss = S.toList tpsset
                  in instClass ft tpss
                --if normal, you already have the (p,s)
                Left ps ->
                  let Right ps' = instT v2t ps
                  in return ps'
      --add it to the map; note that must be done before recursive exploration
      --to prevent an infinite loop
      modify (\ms -> ms{exploredFuns = M.insert (f,monoTs) (ft,ps) $
                         exploredFuns ms})
      --recursively explore it
      explore ps

--Given a monomorphic type, select the first instance that matches it and mono
--that; error if none do.
instClass :: T -> [(T,Pat,S)] -> Mono (Pat,S)
instClass ft tpss = go tpss
  where go = \case
          [] -> throwError $ NoInstanceForClass ft $ map (\(t,_,_)->t) tpss
          (t,p,s):tpss ->
            case bindT t ft of
              Right v2t ->
                let Right ps' = instT v2t (p,s)
                in return ps'
              _ -> go tpss
--monoGlobal g:
--If it has no initializer, return
--otherwise recursively explore it
monoGlobal :: Name -> Mono ()
monoGlobal g = withError (InMonoGlobal g) $ do
  b <- gets $ S.member g . exploredGlobals
  if b
    then return ()
    else do
    modify (\ms -> ms{exploredGlobals = S.insert g $
                     exploredGlobals ms})
    (r,me) <- (! g) <$> asks globals
    case me of
      Nothing -> return ()
      Just e -> explore e

--monoDT tycon monoTs:
--Check it's not explored
--For each constructor:
-- Look up polymorphic tag expr and (DT params, tag type)
-- subst params for monoTs in tag expr, then recursively explore.
--Most complex scenario: the tag contains a class function
--TODO use lenses so I can write a clean, shared checkExplored elem field
monoDT :: Name -> [T] -> Mono ()
monoDT tycon monoTs = withError (InMonoDT (tycon,monoTs)) $ do
    b <- gets $ M.member (tycon,monoTs) . exploredDTs
    if b
      then return ()
      else do
      dtsi <- asks dtsInfo
      let Just dsi = M.lookup tycon $ datatypes dtsi
          params = dtParams dsi
          v2t = M.fromList $ zip params monoTs
          cons = dtCanonicalCons dsi
          cis = conInfo dtsi
      con2e <- M.fromList <$> forM cons (\con -> do
                                           let Just (UBCon{conTag=e}) =
                                                 M.lookup con cis
                                               Right e' = instT v2t e
                                           return (con,e'))
      modify (\ms -> ms{exploredDTs = M.insert (tycon,monoTs) con2e $
                         exploredDTs ms})
      explore con2e

--Find all mentions of functions, globals and datatypes that need to be mono'd.
--Functions: Var f@ts | f in defuns => monoFun f ts
--Globals: TypedVar nm _ | M.member nm (globals m)
--Datatypes:
--Constructors:
-- E: con@ts | con in conInfo (dtsInfo m)
-- P: Con args
-- P: Con {field: p}
--Fields:
-- E: e.field
-- P: Con {field: p} --redundant
--Note a bunch of redundant empty-bodied defs of primfuns get added.
--Two separate traversals to avoid weird type error.
explore :: Data a => a -> Mono ()
explore a = do
  everywhereM (mkM $ \e -> do
                  case e of
                    --Global
                    TypedVar mt nm -> do
                      b <- asks (M.member nm . globals)
                      if b
                        then monoGlobal nm
                        else return ()
                    --Function or constructor
                    TyApp nm ts -> do
                      b <- asks (M.member nm . defuns)
                      if b
                        then monoFun nm ts
                        --It must be a constructor; look up the parent tycon
                        else exploreCon nm ts
                    ConRecord con mts _ ->
                      case mts of
                        Nothing -> error "Compiler error: ConRecord not HM'd!"
                        Just ts -> do
                          exploreCon con ts
                    Dot _ mts field ->
                      case mts of
                        Nothing -> error "Compiler error: Dot not HM'd!"
                        Just ts -> do
                          exploreField field ts
                    _ -> return ()
                  return e
                    ) a
  everywhereM (mkM $ \p -> do
                  case p of
                    Deref (Just ts) e -> monoFun "deref" ts
                    PDot (Just ts) _ field -> do
                      exploreField field ts
                    PBang (Just ts) _ _ -> monoFun "indexArray" ts
                    PConArgs con (Just ts) _ ->
                      exploreCon con ts
                    PCon con (Just ts) _ ->
                      exploreCon con ts
                    _ -> return ()
                  return p
              ) a
  return ()

exploreCon :: Name -> [T] -> Mono ()
exploreCon con ts = do
  tycon <- getConParent con
  monoDT tycon ts
exploreField :: Name -> [T] -> Mono ()
exploreField field ts = do
  tycon <- getFieldParent field
  monoDT tycon ts
--Get the DT which contains the constructor
getConParent :: Name -> Mono Name
getConParent con = do
  dtsi <- asks dtsInfo
  let Just ci = M.lookup con $ conInfo dtsi
  return $ conParent ci
--Ditto for a field
getFieldParent :: Name -> Mono Name
getFieldParent field = do
  dtsi <- asks dtsInfo
  let Just fi = M.lookup field $ fieldInfo dtsi
  case fi of
    IsTag tycon ->
      return tycon
    IsNormal _ tycon ->
      return tycon

--Given a polymorphic type poly with all tysyns expanded
--and a monomorphic type mono,
--finds an assignment m of poly's tyvars to monotypes s.t. poly/m = mono.
--Iff that's not possible, returns Nothing.
bindT :: T -> T -> Either BindError (Map Name T)
bindT poly mono = runExcept $ execStateT (go (poly,mono)) M.empty
  where go :: (T,T) -> StateT (Map Name T) (Except BindError) ()
        go = \case
          (TyVar v, t) -> do
            mt <- gets (M.lookup v)
            case mt of
              Just t' ->
                complainIf (t /= t') $ ConflictingBinds v t t'
              Nothing -> modify (M.insert v t)
          (fp :$$ xp, fm :$$ xm) -> go (fp,fm) >> go (xp,xm)
          (t, t') -> complainIf (t /= t') $ Can'tBind t t'
                        
data BindError = ConflictingBinds Name T T
               | Can'tBind T T
  deriving (Eq,Ord,Read,Show)
--instT m poly = poly/m
--Throws v if there's an unrecognized var v in poly
--Generic 
instT :: Data a => Map Name T -> a -> Either Name a
instT m = everywhereM $ mkM $ \case
  TyVar v ->
    case M.lookup v m of
      Just t -> return t
      Nothing -> Left v
  t -> return t
