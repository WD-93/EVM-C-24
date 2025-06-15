{-# LANGUAGE LambdaCase #-}
module Desugar.Globals (desugarGlobals) where
--Converts all occurrences of g where g in globals to *g in both E and Pat.
--Then g is a Ptr r a, where a is its source-visible type and r is its
--declared region.
--g : a tysigs must be converted to g : Ptr r a during HM.
--The initial type of a global with a bound expr but no sig is Ptr r tau;
--memory g = e unifies t = typeOf e with tau; the resulting type of g is
--Ptr Memory t.

import AST.DTs

import Data.Generics (everywhere,mkT,extT)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Typeable (Typeable)

--A weird type error prevents me from merging the traversals using extT...
desugarGlobals :: Module -> Module
desugarGlobals m =
  let gs = M.keysSet $ globals m
      isGlobal = flip S.member gs
      desugarE :: E -> E
      desugarE = \case
        Var g | isGlobal g -> Var "deref" :$ Var g
        e -> e
      desugarP :: Pat -> Pat
      desugarP = \case
        PVar g | isGlobal g -> Deref (Var g)
        p -> p
  in everywhere (mkT desugarP) $ everywhere (mkT desugarE) m
