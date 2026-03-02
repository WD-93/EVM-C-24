module Core.SSA (ssa) where

import Core.RestrictedCore

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Generics (Data(..), everywhere, mkT, everything, mkQ,
                      everywhereM, mkM)
import Control.Monad.State
import Control.Monad (forM_)

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
--SSA can't fail unless a Core function is malformed due to:
--1) A var repeated in fun or op lhs
--2) A var is used without being bound by op or fun lhs.
--That must be due to a compiler error, so we throw a Haskell exception.
--Problem: that exception may be caught late if it's deep in the object
--graph.
ssa :: Core -> OptCore
ssa core =
  Core {coreDefuns = M.map ssaFun $ coreDefuns core,
        coreStatic = coreStatic core
       }
--Note: the vars in the BranchValue and branch need to be updated as well.
ssaFun :: (BranchValue,
           FunRHS_ [(Value,OpE)]) ->
          (BranchValue,
           FunRHS_ (Map Var (Value,OpE)))
ssaFun (lhs,(ops,branch)) =
  (everywhere (mkT $ giveVersion 1) lhs,
   let (ops',var2ver) = execState (ssaOps ops) (M.empty,initialVerMap)
   in (ops', everywhere (mkT $ applyVersion var2ver) branch)
  )
  --All vars in the lhs must map to 1.
  --If a var is repeated, that's a compiler error.
  where initialVerMap =
          M.fromSet (const 1) $ collectVars lhs
          
--Throws an exception if vars are repeated.
collectVars :: Data a => a -> Set Var
collectVars = foldr (\v s ->
                       if S.member v s
                       then error $ "Compiler error: repeated var " ++ show v
                       else S.insert v s)
              S.empty .
              --Is this accidentally quadratic..?
              everything (++) (mkQ [] $ \v@Mono{} -> [v])

type SSAM = State (Map Var (Value, OpE), Map Var Int)
--For each op (lhs,(op,rhs)) in ops,
-- replace rhs according to the current version map;
-- for each var in lhs, bump its version number
--Vars in the rhs which have not been bound by an op or the lhs should
--raise a compiler error.
--As such, vars in the lhs must be present in the version map from the
--start.
ssaOps :: [(Value,OpE)] -> SSAM ()
ssaOps = mapM_ ssaOp
ssaOp :: (Value,OpE) -> SSAM ()
ssaOp (lhs,(op,rhs)) = do
  var2ver <- gets snd
  --The exception hides in the OpE...
  let rhs' = everywhere
        (mkT $ \v ->
            case M.lookup v var2ver of
              Nothing ->
                error $ "Compiler error: unbound var "
                ++ show v
              Just ver -> giveVersion ver v) rhs
  --Collect each var in lhs; error if there are duplicates
  let vs = S.toList $ collectVars lhs
  --Bump the version of each var; if unbound, give it version 1.
  forM_ vs (\v -> do
               (opmap,var2ver) <- get
               let ver = case M.lookup v var2ver of
                           Nothing -> 1
                           Just n -> n + 1
               put (opmap, M.insert v ver var2ver)
           )
  --Substitute the vars in the lhs according to their new version.
  var2ver <- gets snd
  let lhs' = everywhere (mkT $ \v ->
                            case M.lookup v var2ver of
                              Just ver -> giveVersion ver v
                              Nothing -> error "!!?") lhs
  --Bind each substited var to their SSA'd parent op.
  let parentOp = (lhs',(op,rhs'))
  everywhereM (mkM $ \v -> do
                  (opmap,var2ver) <- get
                  put (M.insert v parentOp opmap,
                       var2ver)
                  return v) lhs'
  return ()

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
