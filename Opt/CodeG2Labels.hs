module Opt.CodeG2Labels where

import AST.DTs (Name(..))
import Core.RestrictedCore
import Const.Const (Serialized(..))
import Opt.AbVar
import Opt.Semilattice

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad

--Core has no code state variable; the meaning of codecopy off a code global
--label is therefore implicit in the coreStatic field of Core.
--A codecopy(to,from,len) has, to a first approximation, the effect of
--writing the labels and bytes found in all the codeGs from might reference to
--memory.
--The OpFun type in Opt.AI.EVM therefore needs to be parameterized by a
--mapping from codeG name to an AbVar containing all the labels it
--references.
--One may assume codecopy may write an arbitrary constant as well, unless it
--only consists of zero bytes.
--Node that codecopy(to,from,32) for from -> a nonzero constant k should still
--set memory's possKs to All rather than k, since a later mload might read a
--partial slice of it. For finer-grained memory modeling, I should use a stack
--of states and a linear model for alloc.

--Note that any CodeGError is a compiler error; user error should not be able
--to produce malformed Core.
--That's good, because AI has no MonadError effect...
data CodeGError = UndefinedLabel Name
                | BadLabelOffLen (Int,Int) Name --only (0,2) accepted for now
  deriving (Eq,Ord,Read,Show)
codeG2Labels :: Core_ a -> Either CodeGError (Map Name AbVar)
codeG2Labels core = mapM (ser2Abstract core) $ coreStatic core

ser2Abstract :: Core_ a -> Serialized -> Either CodeGError AbVar
ser2Abstract core ser
  --If ser is all zeroes (which includes empty), it's K 0
  | all (\x -> case x of
            Left ns -> all (==0) ns
            _ -> False) $ serContent ser = return $ exactly 0
  --Otherwise collect all labels; possKs = All
  | let = do
          let offlenlabs = [tup | Right tup <- serContent ser]
          abvs <- forM offlenlabs
            (\(off,len,lab) ->
                if (off,len) /= (0,2)
                then Left $ BadLabelOffLen (off,len) lab
                else do
                  lt <- typeOfLabel core lab
                  return $ label lt lab)
          return $ foldr (\/) bottom{possKs=All} abvs

--Precondition: a serialized expr will never mention a JT
typeOfLabel :: Core_ a -> Name -> Either CodeGError LabelType
typeOfLabel core nm
  | M.member nm $ coreDefuns core = return Fun
  | M.member nm $ coreStatic core = return CodeG
  | let = Left $ UndefinedLabel nm
