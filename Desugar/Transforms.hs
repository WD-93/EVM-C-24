{-# LANGUAGE LambdaCase #-}
module Desugar.Transforms where

import AST.DTs

import Control.Arrow ((***))

--When desugaring a && b to a block expr, a and b may contain explicit local
--returns. Those must be incremented if they're "free".
--The transformation is analogous to embedding an expr into a lambda using
--de Bruijn indexing for variables.
incLRDepth :: Int -> E -> E
incLRDepth = go
  where go n = \case
          BlockE ss -> BlockE $ map (incLRDepthS (n+1)) ss
          f :$ x -> go n f :$ go n x
          PrimOp nm es -> PrimOp nm $ map (go n) es
          EStruct fields -> EStruct $ map (\(pad,mnm,e) ->
                                             (pad,mnm,go n e)) fields
          Dots e fs -> Dots (go n e) fs
          Coerce t e -> Coerce t (go n e)
          Con nm e -> Con nm (go n e)
          e :@ (p,pe) -> go n e :@ (incLRDepthP n p, go n pe)
          p := e -> incLRDepthP n p := go n e
          e -> e
incLRDepthS :: Int -> S -> S
incLRDepthS = go
  where go n = do
          let goe = incLRDepth n
              gop = incLRDepthP n
          \case
            Return e -> Return $ goe e
            Ifte b s1 s2 -> Ifte (goe b) (go n s1) (go n s2)
            While e s -> While (goe e) (go n s)
            Case e conpss -> Case (goe e) $ map (\(con,p,s) ->
                                                   (con,gop p, go n s)) conpss
            Block ss -> Block $ map (go n) ss
            LocalReturn m e ->
              LocalReturn (if m >= n then m+1 else m) (goe e)
            SE e -> SE $ goe e
            s -> s
incLRDepthP :: Int -> Pat -> Pat
incLRDepthP n = r
  where
    r = \case
      PStruct mnmps -> PStruct $ map (id *** r) mnmps
      PTup ps -> PTup $ map r ps
      PDot p nm -> PDot (r p) nm
      PHash p ix -> PHash (r p) ix
      Deref e -> Deref $ incLRDepth n e
      p -> p
