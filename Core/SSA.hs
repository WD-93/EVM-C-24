{-# LANGUAGE LambdaCase #-}
module Core.SSA (ssa) where

import Core.RestrictedCore
import Util ((?))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics (Data(..), everywhere, mkT, everything, mkQ,
                      everywhereM, mkM)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad (forM, forM_)

--After Core.Convert, the core module contains a map
--fname => (lhs,rhs), where each fname corresponds to a basic block.
--The rhs is a list of straight-line ops followed by a branch.
--Ops are of form ws1;ss1 = op ws2;ss2, where ws;ss is a pair of
--lists of word vars (ws) and state vars (ss).
--op may be either an EVM instruction mnemonic or "copy", indicating a
--single word var copy.
--Ops must initially be in a list because variables can be reassigned, meaning
--order matters.
--The SSA transformation replaces all mutable variables x with x!<n>, where
--n is the version (starting with 1). The nth value x takes in the function
--rhs is replaced with x!<n>.
--Copy ops are also eliminated; if x = copy y, then any subsequent use of x
--until it's next assigned is replaced with y.
--As such, order of operations no longer matters. Instead of a list,
--the straight-line part of the function rhs becomes a map SSA var => the op
--that produced it. Note ops which produce multiple vars will contain an
--entry for each var.
--Vars present in the branch but not the map must be in the lhs.

--The program repr Opt works on.
type OptCore = Core_ (Map Var (Value,OpE))
--SSA can only fail if a Core function is malformed due to:
--1) A var repeated in fun or op lhs
--2) A var is used without being bound by op or fun lhs.
--3) A copy op (the only op inspected by SSA) has the wrong arg or ret arity
--That must be due to a compiler error.
--For now we only report the first malformed function.
data SSAError = MalformedFunLHS BranchValue Var
              | MalformedOpLHS Value Var
              | UnboundVar Var
              | MalformedCopy Value Value
ssa :: Core -> Either (FunVar,SSAError) OptCore
ssa core = do
  let fdefs = M.toList $ coreDefuns core
  fdefs' <- forM fdefs (\(f,def) ->
                          ((,) f <$> runExcept (evalStateT (ssaFun def)
                          (SSAS M.empty M.empty M.empty)))
                          ? ((,) f)
                       )
  return Core {coreDefuns = M.fromList fdefs',
               coreStatic = coreStatic core
              }
--Note: the vars in the BranchValue and branch need to be updated as well.
ssaFun :: (BranchValue,
           FunRHS_ [(Value,OpE)]) ->
          SSAM
          (BranchValue,
           FunRHS_ (Map Var (Value,OpE)))
ssaFun (lhs,(ops,branch)) = do
  lhs' <- ssaFunLHS lhs
  mapM_ ssaOp ops
  branch' <- ssaVars branch
  opmap <- gets opMap
  return (lhs',(opmap,branch'))
--Substitutes all vars in a DS
ssaVars :: Data a => a -> SSAM a
ssaVars = everywhereM (mkM ssaVar)
--Converts the vars in the LHS to SSA vars; errors if there are
--duplicate vars.
ssaLHS :: Data a => (a -> Var -> SSAError) -> a -> SSAM a
ssaLHS malformed lhs =
  let vs = listVars lhs
  in case reportDuplicate vs of
       Just v -> throwError $ malformed lhs v
       Nothing -> do
         mapM_ bumpVar vs
         ssaVars lhs
ssaFunLHS :: BranchValue -> SSAM BranchValue
ssaFunLHS = ssaLHS MalformedFunLHS
ssaOpLHS = ssaLHS MalformedOpLHS

--First give v its version (v => v!n), then apply the substmap.
ssaVar :: Var -> SSAM Var
ssaVar v = do
  vermap <- gets verMap
  substmap <- gets substMap
  case M.lookup v vermap of
    Nothing -> throwError $ UnboundVar v
    Just ver ->
      let v' = giveVersion ver v
      in return $ case M.lookup v' substmap of
                    Nothing -> v'
                    Just v'' -> v''
--If v is unbound, give it version 1; otherwise increment the version.
bumpVar :: Var -> SSAM ()
bumpVar v = do
  s <- get
  let vermap = verMap s
      ver' = case M.lookup v vermap of
               Nothing -> 1
               Just ver -> ver+1
  put s{verMap = M.insert v ver' vermap}

--Helper functions.
--Is listVars accidentally quadratic...?
listVars :: Data a => a -> [Var]
listVars = everything (++) (mkQ [] $ \v@Mono{} -> [v])
--Reports the first duplicate found.
reportDuplicate :: Ord a => [a] -> Maybe a
reportDuplicate = go S.empty
  where go s = \case
          [] -> Nothing
          a:as -> if S.member a s
                  then Just a
                  else go (S.insert a s) as

type SSAM = StateT SSAS (Except SSAError)
data SSAS = SSAS {opMap :: Map Var (Value, OpE), --var => parent op
                  verMap :: Map Var Int, --var => version
                  --post-SSA var => the post-SSA var it's a copy of.
                  substMap :: Map Var Var
                 }
  deriving (Eq,Ord,Read,Show)
--For each op (lhs,(op,rhs)) in ops,
-- replace rhs according to the current version map;
-- for each var in lhs, bump its version number
--Vars in the rhs which have not been bound by an op or the lhs should
--raise a compiler error.
--As such, vars in the lhs must be present in the version map from the
--start.
--I forgot to eliminate copies! Need an additional subst map
--post-SSA var => post-SSA var.
ssaOp :: (Value,OpE) -> SSAM ()
--Copy ops are eliminated; subsequent references to x until the next
--assignment are replaced with the version of y current at the time of
--the copy.
ssaOp (([x],[]),(Op "copy",([y],[]))) = do
  y' <- ssaVar y
  bumpVar x
  x' <- ssaVar x
  modify (\s -> s{substMap = M.insert x' y' $ substMap s})
--copy ops with the wrong argument or return arity trigger an error.
ssaOp (lhs,(Op "copy",rhs)) = throwError $ MalformedCopy lhs rhs
ssaOp (lhs,(op,rhs)) = do
  rhs' <- ssaVars rhs
  lhs' <- ssaOpLHS lhs
  let vs = listVars lhs'
      parentOp = (lhs',(op,rhs'))
  forM_ vs (setParentOp parentOp)
setParentOp :: (Value,OpE) -> Var -> SSAM ()
setParentOp parent v = modify
  (\s -> s{opMap = M.insert v parent $ opMap s})

--Give a var a version n: v:t => v!<n>:t
giveVersion :: Int -> Var -> Var
giveVersion n v = v{nameOfVar = nameOfVar v ++ "!" ++ show n}

--Given a var => ver map (default 1), transform v:t into v!<n>:t, where n
--is its version in the map.
applyVersion :: Map Var Int -> Var -> Var
applyVersion var2ver var =
  giveVersion (getVersion var2ver var) var
--Default 1.
getVersion :: Map Var Int -> Var -> Int
getVersion var2ver var =
  case M.lookup var var2ver of
    Nothing -> 1
    Just n -> n
