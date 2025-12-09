{-# LANGUAGE LambdaCase #-}
module Unshadow.Unshadow where

--A simple transformation: each local is given a unique name to ensure that
--none shadow each other.
--Each local x in source location L is changed to x#n, where n is the number of
--locals named x which are semantically live (i.e. on the stack in a naive
--compilation) at point L. # is used because vars may not contain # in
--source, ensuring there's no confusion with other vars.
{-Example:
f x := {
 var x = 1;
 while(x) {
  var x = 2;
  x++
 }
} =>
f x#1 := {
 var x#2 = 1;
 while(x#2) {
  var x#2 = 2;
  x#2++
 }
}
-}
--TODO this transformation earlier; HM could benefit from it.

import AST.DTs
import AST.Util (freeVarsPat)
import Mono.Mono (MonoS(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Data.Generics
import Control.Arrow ((***))
import Control.Monad (forM)

{-Algo:
For each function f p := s in explored funs,
find nms in p and declare a new var for each. Precondition: no duplicate vars,
no patterns containing Es. TODO enforce that.
Exploring s:
Block resets scope; ifte, while, case have implicit blocks.
var x = e => transform e, scope[x]++
E and Pat are trivial since they don't affect scope; just apply the scope map.
-}

--unshadow must now operate on Module... only defuns is affected.
--Apply unshadowFun to each ordinary defun and instance.
unshadow :: Module -> Module
unshadow mod = mod{defuns = M.map (\case
                                      Left ps -> Left $ unshadowFun ps
                                      Right tpses ->
                                        --Note unshadowFun is injective
                                        Right $ S.map
                                        (\(t,p,s) ->
                                            let (p',s') = unshadowFun (p,s)
                                            in (t,p',s')) tpses
                                      ) $
                    defuns mod
                  }
{-
unshadow :: MonoS -> MonoS
unshadow ms = ms{exploredFuns =
                    M.map (id *** unshadowFun) $
                    exploredFuns ms
                }
-}              

type Unshadow = State (Map Name Int)
--Precondition: no name in m contains #
--Note globals and functions are not affected
unshadowTerm :: Data a => Map Name Int -> a -> a
unshadowTerm m = everywhere (mkT $ \case TypedVar mt nm
                                           | Just n <- M.lookup nm m ->
                                             TypedVar mt (nm++"#"++show n)
                                         e -> e
                            ) .
                 everywhere (mkT $ \case TypedPVar mt nm
                                           | Just n <- M.lookup nm m ->
                                             TypedPVar mt (nm++"#"++show n)
                                         p -> p)
unshadowFun :: (Pat,S) -> (Pat,S)
unshadowFun (p,s) =
  let verMap = M.fromSet (const 1) $ freeVarsPat p
      s' = evalState (unshadowS s) verMap
  in (unshadowTerm verMap p, s')

unshadowS :: S -> Unshadow S
unshadowS = go
  where go = \case
          SE e -> SE <$> ue e
          Return e -> Return <$> ue e
          Ifte i t e ->
            Ifte <$> ue i <*> block (go t) <*> block (go e)
          While e s ->
            While <$> ue e <*> go s
          Case e cases ->
            Case <$> ue e <*> forM cases (\(pat,s) ->
                                            (,) <$> ue pat <*> block (go s))
          Block ss -> Block <$> block (mapM go ss)
          Break -> return Break
          Continue -> return Continue
          --The tricky part. Note the same var may be declared multiple times.
          Declare varEs -> Declare <$>
                           forM varEs (\(var,e) -> do
                                          e' <- ue e --it's in the old scope
                                          vm <- get
                                          let oldver = case M.lookup var vm of
                                                         Nothing -> 0
                                                         Just n -> n
                                              ver = oldver + 1
                                          modify (M.insert var ver)
                                          return (var++"#"++show ver, e'))
        ue :: Data a => a -> Unshadow a
        ue = gets . flip unshadowTerm
        block m = do
          s <- get
          a <- m
          put s
          return a
        
