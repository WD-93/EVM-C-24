module Opt.AbVar where

import Opt.Semilattice

import Data.Set (Set(..))
import qualified Data.Set as S

--Defines abstract vars, the abstract value of Core IR vars.

--Abstract variables; can represent both stack and state vars.
type Byte = Int
type Label = String --assumed to be a 2-byte label
data LabelType = Fun | JT | CodeG
  deriving (Eq,Ord,Read,Show)
--Integer should be cheaper than 32 Ints; I don't need to represent symbolic
--bytes here. It may be expensive for &, <<.
--There's no need for a separate Exactly label; it can be represented as
--{{f},{},{}, mayBeK = False}
--By extending the possible k values lattice, AbVar can be represented using
--a single constructor: a quadruplet of lattices.
--For now, region state vars are S, just containing mentioned label info.
--"One of fs" and "An expression mentioning fs" are two different things;
--however, f + g may either be f, g or an arbitrary k. That captures the
--concept of "expression mentioning".
--When applying EVM ops, information may flow from labels to constants,
--but never in the opposite direction.
data AbVar = S {funs :: Set Label,
                jts :: Set Label,
                codeGs :: Set Label,
                possKs :: PossKs
               }
  deriving (Eq,Ord,Read)
--It would be nice to be able to separate defining the derived dict from
--setting it as the Show instance.
instance Show AbVar where
  show abv
    | S.null $ S.unions $
      map ($ abv) [funs,jts,codeGs] = show $ possKs abv
    | Just (lt,lab) <- unlabel abv = show lt ++ ":" ++ lab
    | let = "S {funs = " ++ show (funs abv) ++
            ", jts = " ++ show (jts abv) ++
            ", codeGs = " ++ show (codeGs abv) ++
            ", possKs = " ++ show (possKs abv)
--An abstract value may mention labels or consist of constants.
--Labels are to be "garbage-collected" during optimization, eliminating
--functions, jump tables and code globals which are never used or (better yet)
--never mentioned in reachable BBs.
--TODO useful extension: byte length or nonzero ranges.
data PossKs = None | K Integer | All --invariant: 0 <= n < 2^256
  deriving (Eq,Ord,Read)
instance Show PossKs where
  show pks =
    case pks of
      None -> "_|_"
      K n -> show n
      All -> "*"
instance JoinSemilattice PossKs where
  None \/ x = x
  x \/ None = x
  K n \/ K m
    | n == m = K n
  _ \/ _ = All
instance HasBottom PossKs where
  bottom = None
instance HasTop PossKs where
  top = All
--TODO look at deriving plugin machinery
instance JoinSemilattice AbVar where
  s1 \/ s2 = S{funs = funs s1 \/ funs s2,
               jts = jts s1 \/ jts s2,
               codeGs = codeGs s1 \/ codeGs s2,
               possKs = possKs s1 \/ possKs s2
              }
instance HasBottom AbVar where
  bottom = S S.empty S.empty S.empty None
exactly :: Integer -> AbVar
exactly n = bottom{possKs = K n}
label lt lab =
  let labs = S.singleton lab
  in case lt of
       Fun -> bottom{funs = labs}
       JT -> bottom{jts = labs}
       CodeG -> bottom{codeGs = labs}
--Returns Just n iff the abvar is exactly n
unexactly ab
  | K n <- possKs ab =
      if ab == exactly n
      then Just n
      else Nothing
  | let = Nothing
--Returns Just (lt,lab) iff the abvar is label lt lab
--Labels of different label type are disjoint
--If their union contains 1 element
unlabel :: AbVar -> Maybe (LabelType,String)
unlabel ab
  | possKs ab == None =
    let fs = funs ab
        js = jts ab
        cs = codeGs ab
    --Avoids computing the union just to discard it
    in if sum (map S.size [fs,js,cs]) == 1
       then case () of
              _ | S.size fs == 1 -> Just (Fun, S.findMin fs)
                | S.size js == 1 -> Just (JT, S.findMin js)
                | S.size cs == 1 -> Just (CodeG, S.findMin cs)
       else Nothing
  | let = Nothing
