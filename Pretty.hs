{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Pretty where

import Data.List (intercalate)
import Data.Map (Map(..))
import qualified Data.Map as M
import qualified Data.Set as S

import DTs (Name(..),T(..),Padding(..),pattern (:->),pattern UInt, pattern SInt)
import IR1
import ToyCFG

--Just a test module for viewing intermediate compiler output

prettyIRM :: IRModule -> [String]
prettyIRM irm =
  let ds = M.toList $ irDefuns irm
  in ds >>= (\(f,irs) ->
               [f ++ ":"] ++
               map (' ':) (irs >>= prettyIR))
--Given a pretty for vs and a [(Name,v)], generates
--k:
-- pretty v
-- ...
prettyBindings :: (v -> [String]) -> [(Name,v)] -> [String]
prettyBindings pretty nmvs =
  let ds = nmvs
  in ds >>= (\(f,irs) ->
               [f ++ ":"] ++
               map (' ':) (pretty irs))

--IR => lines
prettyIR :: IR -> [String]
prettyIR = do
  let r = prettyIR
  \case
    Op _ nmts op nms -> [unwords [showLHS nmts,"=",showOp op,showRHS nms]]
    Ifte _ nm th el ->
      ["ifte "++nm++" then"] ++
      indentBlock th ++
      ["else"] ++
      indentBlock el
    While () pre v post -> ["while {"] ++
      indentBlock pre ++
      ["}"] ++
      [v] ++
      ["{"] ++
      indentBlock post ++
      ["}"]
    Return _ nms -> ["return " ++ showRHS nms]
indentBlock irs = map (' ':) (irs >>= prettyIR)

showLHS :: [(Name,IRT)] -> String
showLHS = intercalate ", " . map showNMT
showNMT (nm,irt) = nm ++ " : " ++ showIRT irt
showIRT = \case
  Mem -> "Mem"
  Word n t -> showT t ++ "#" ++ show n
showT = do
  let r = showT
  \case
    UInt n -> "uint"++show n
    SInt n -> "int"++show n
    a :-> b -> "(" ++ r a ++ " -> " ++ r b ++ ")"
    TyCon nm -> nm
    tf :$$ tx -> r tf ++ " " ++ r tx
    TyNat n -> show n
    tup | Just ts <- unTupleT tup ->
          "(" ++ intercalate ", " (map showT ts) ++ ")"
    Struct fields -> "{" ++ intercalate ", " (map showFieldT fields) ++ "}"
showFieldT (padding,mnm,t) =
  let p = case padding of
            BitPad -> ["bitpad"]
            BytePad -> []
            WordPad -> ["wordpad"]
      n = case mnm of
            Nothing -> []
            Just nm -> [nm,":"]
  in unwords $ p ++ n ++ [showT t]
               
showOp = \case
  Push (Const n) -> show n
  Push (LabelConst l) -> "$" ++ l
  Opcode op -> op
  Call -> "call"
  Reduce op -> "reduce(" ++ op ++ ")"
  Copy -> "copy"
showRHS = intercalate ", "


showCFGM :: Map Name (LL,CFGS) -> [String]
showCFGM = prettyBindings showCFG . M.toList
--Show the CFG for a single function
--The LL is the function entry point and its live vars
--Show SLCs in DFS order from entry point
showCFG :: (LL,CFGS) -> [String]
showCFG llcfgs =
  dfsCFG llcfgs >>= showSLC
  

showSLC :: (Label, SLC Name) -> [String]
showSLC (l,slc) =
  let live = S.toList $ slcLive slc
      ops = map (\(lhs,op,rhs) -> Op () lhs op rhs) $ slcOps slc
      branch = slcBranch slc
  in
  --labelID(x,y,z): where x,y,z are live
  [show l ++ "(" ++ showRHS live ++ "):"] ++
  map (' ':) (ops >>= prettyIR) ++
  [unwords $ case branch of
      Jump l -> ["jump",show l]
      Jumpi v th el -> ["jumpi",v,show th,show el]
      BReturn vs -> ["return","(" ++ showRHS vs ++ ")"]
  ]

--After SSA and copy elim
--Nodes are generated in DFS order from start and then pruned for reachability,
--so showing SLCs in reverse order should 
showCFG2 :: Map Name (Label,Map Label SLC2) -> [String]
showCFG2 = undefined
