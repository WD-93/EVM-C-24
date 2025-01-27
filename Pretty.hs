{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Pretty where

import Data.List (intercalate)
import Data.Map (Map(..))
import qualified Data.Map as M
import qualified Data.Set as S

import DTs (Name(..),T(..),Padding(..),pattern (:->),pattern UInt, pattern SInt)
import IR1
import ToyCFG
import Asm hiding (Asm(Opcode,Push),Label())
import qualified Asm as A

--Just a test module for viewing intermediate compiler output

prettyIRM :: IRModule -> [String]
prettyIRM irm =
  let ds = M.toList $ irDefuns irm
  in ds >>= (\(f,(arity,irs)) ->
               [f ++ "(arity " ++ show arity ++ ")"++ ":"] ++
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
  W n t -> showT t ++ "#" ++ show n
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
showFieldT ((pad,al),mnm,t) =
  let p = case pad of
            Bit -> ["pad bit"]
            Byte -> []
            Word -> ["pad word"]
      a = case al of
            Bit -> ["align bit"]
            Byte -> []
            Word -> ["align word"]
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

--Just ignores arity for now
showCFGM :: Map Name (Arity,(LL,CFGS)) -> [String]
showCFGM = prettyBindings (showCFG . (\(arity,(ll,cfgs)) ->
                                        (fst ll,cfgs))) . M.toList
--Show the CFG for a single function
--The LL is the function entry point and its live vars
--Show SLCs in DFS order from entry point
showCFG :: (Label,CFGS) -> [String]
showCFG llcfgs =
  dfsCFG llcfgs >>= showSLC id
  

showSLC :: (v -> String) -> (Label, SLC v) -> [String]
showSLC showV (l,slc) =
  let live = S.toList $ slcLive slc
      ops = map (\(lhs,op,rhs) ->
                   Op () (map (\(v,t) -> (showV v, t)) lhs) op $ map showV rhs)
                  $ slcOps slc
      branch = slcBranch slc
  in
  --labelID(x,y,z): where x,y,z are live
  [show l ++ "(" ++ showRHS live ++ "):"] ++
  map (' ':) (ops >>= prettyIR) ++
  [unwords $ case branch of
      Jump l -> ["jump",show l]
      Jumpi v th el -> ["jumpi",showV v,show th,show el]
      BReturn vs -> ["return","(" ++ showRHS (map showV vs) ++ ")"]
  ]

--After SSA and copy elim
--Nodes are generated in DFS order from start and then pruned for reachability,
--so showing SLCs in reverse order should ensure they're presented in jump
--order?
--No, for while (1) do {} it's not in jump order.
showCFG2M :: (Map Name (Arity,(Label, Map Label SLC2))) -> [String]
showCFG2M = prettyBindings showCFG2 . M.toList
--Just ignores arity for now
showCFG2 :: (Arity,(Label,Map Label SLC2)) -> [String]
showCFG2 (arity,(lab,cfg2)) =
  --let m = M.map (\(slc,verMap,substMap,inEdgeCount) -> slc) cfg2 in
  dfsGraph slc2Children lab cfg2 >>=
  showSLC2
showSLC2 :: (Label,SLC2) -> [String]
showSLC2 (lab,(slc,ver,sub,rc)) =
  --["Ver: " ++ prettyMap id show ver,
  -- "Sub: " ++ prettyMap prettySSA prettySSA sub,
  -- "Refcount: " ++ show rc] ++
  showSLC prettySSA (lab,slc)
prettyMap :: (k -> String) -> (v -> String) -> Map k v -> String
prettyMap showK showV m =
  intercalate ", " $ map (\(k,v) -> showK k ++ ": " ++ showV v) $ M.toList m
prettySSA :: SSAName -> String
prettySSA (ix,nm) = nm ++ "[" ++ show ix ++ "]"

prettyAsm :: A.Asm -> String
prettyAsm = \case
  A.Push len n -> "push" ++ show len ++ " " ++ show n
  PushLabel len lab -> "push" ++ show len ++ " " ++ prettyAsmLabel lab
  Dup n -> "dup" ++ show n
  Swap n -> "swap" ++ show n
  A.Opcode str -> str
  PlaceLabel lab -> prettyAsmLabel lab ++ ":"
  DefLabel lab lv -> prettyAsmLabel lab ++ " = " ++ show lv
  Bytes bs -> "bytes " ++ show bs
  UseLabel len lab -> prettyAsmLabel lab ++ ":" ++ show len
  Comment str -> "; " ++ str
prettyAsmLabel = \case
  LAnon n -> show $ "anon" ++ show n
  LNamed str -> str
