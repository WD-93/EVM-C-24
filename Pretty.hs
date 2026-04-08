{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Pretty where

import AST.DTs (Name(..),T(..),
                pattern (:->),pattern UInt, pattern SInt,
                unTupleT)
import Core.RestrictedCore
import Structured.DTs
import Const.Const (Serialized(..),SerElem(..))
--import IR1
--import ToyCFG
import Asm hiding (Asm(Opcode,Push),Label())
import qualified Asm as A

import Data.List (intercalate,intersperse)
import Data.Map (Map(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (intToDigit)
import Control.Monad (filterM)

--Just a test module for viewing intermediate compiler output
--Updating it to print the DTs of the new compiler... TODO use actual ppr.
--TODO add a verbosity flag so I can read args and scope without type
--boilerplate.
prettyStructured :: Structured -> [String]
prettyStructured s =
  prettyStructuredFuns (sdefuns s)
prettyStructuredFuns :: Map FunVar (BranchValue,[Stmt]) -> [String]
prettyStructuredFuns f2def = do
  (f,(bv,stmts)) <- M.toList f2def
  [f ++ " " ++ showBranchValue bv ++ " := "]
    ++ indent (stmts >>= prettyStmt)
--It's useful to look at one fun at a time since Structured modules are
--unreadably large before pruning...
prettyStructuredFun :: FunVar -> Structured -> [String]
prettyStructuredFun f s =
  case M.lookup f $ sdefuns s of
    Just (bv,stmts) ->
      [f ++ " " ++ showBranchValue bv ++ " := "]
      ++ indent (stmts >>= prettyStmt)
--(x * y * z * (stk | ()), s1 * s2 * ())
showBranchValue :: BranchValue -> String
showBranchValue (stackWords,mstk,stateVars) =
  "(" ++
  intercalate " * " (map showVar stackWords ++ [showMStk mstk]) ++ ", "
  ++ intercalate " * " (map showVar stateVars ++ ["()"])
  ++ ")"
--nm:t
showVar :: Var -> String
showVar v = nameOfVar v ++ ":" ++ show (typeOfVar v)
showVars :: [Var] -> String
showVars = showTup showVar
showMStk :: Maybe Var -> String
showMStk = \case
  Nothing -> "()"
  Just v -> showVar v
--TODO
prettyStmt :: Stmt -> [String]
prettyStmt = \case
  v1 := (primop,v2) ->
    [showValue v1 ++ " = " ++ showPrimOp primop ++ showValue v2]
  Call scope lhs f rhs ->
    --(x,y,z) = call f(a,b,c) ...scope
    [showVars lhs ++ " = call " ++ showVar f ++ showVars rhs
    ++ " ..." ++ showVars scope]
  -- //scope = (x,y,z) 
  --if condvar in {
  -- cond...
  --} then {
  -- th...
  -- } else {
  -- el...
  --}
  Ifte scope cond condvar th el ->
    [showScope scope,
     "if " ++ showVar condvar ++ " in {"] ++
    indentBlock cond ++
    ["} then {"] ++
    indentBlock th ++
    ["} else {"] ++
    indentBlock el ++
    ["}"]
  While scope cond condvar body ->
    [showScope scope,
     "while " ++ showVar condvar ++ " in {"] ++
    indentBlock cond ++
    ["} do {"] ++
    indentBlock body ++
    ["}"]
  Break scope -> [showScope scope, "break"]
  Continue scope -> [showScope scope, "continue"]
  --Scope shown for debugging purposes
  --return (x,y,z) //scope = (a,b,c)
  Structured.DTs.Return scope vs ->
    [showScope scope,
     "return " ++ showVars vs]
  --I distinguish comments (which have no semantic import)
  --from scope info by using // instead of /#
  Structured.DTs.Comment str -> ["//"++str]
  CaseBranch scope n16 vs tag jt ->
    [showScope $ tag: vs ++ scope,
     "case " ++ (if n16 then "(N16) " else "") ++ showVar tag ++ " of ["] ++
    (concat $ intersperse [","] $ map indentBlock jt) ++
    ["]"]
indentBlock :: [Stmt] -> [String]
indentBlock stmts = indent (stmts >>= prettyStmt)
    
showScope scope = "/#scope = " ++ showVars scope
--(x,y,z)#(s1,s2,...)
showValue :: Value -> String
showValue (stackVs,stateVs) =
  showVars stackVs ++ "#" ++ showVars stateVs

showPrimOp :: PrimOp -> String
showPrimOp = \case
  Push ser -> "push " ++ showSerialized ser
  Op nm -> nm
--(hex | label)* : sizeof
--We don't show len
showSerialized :: Serialized -> String
showSerialized ser =
  "["++ (serContent ser >>= showSerElem) ++ "]:" ++ show (serSizeof ser)
showSerElem :: SerElem -> String
showSerElem = \case
  Left bytes -> bytes >>= showHex
  Right lab -> showLabel lab
--If off == 0: lab:len
--else: lab(off):len
showLabel :: (Int,Int,String) -> String
showLabel (off,len,lab) =
  lab ++ (if off /= 0 then "("++show off++")" else "") ++ ":" ++ show len

--Generic helpers
indent = map (' ':)
showTup f xs = "(" ++ intercalate ", " (map f xs) ++ ")"
--Precondition: the b is in 0..255
showHex b = map intToDigit [b `div` 16, b `mod` 16]

{-
prettyIRM :: IRModule -> [String]
prettyIRM irm =
  let ds = M.toList $ irDefuns irm
      stats = M.toList $ staticData irm
  in (ds >>= (\(f,(arity,irs)) ->
               [f ++ "(arity " ++ show arity ++ ")"++ ":"] ++
               map (' ':) (irs >>= prettyIR))) ++
     ["Labels:"] ++
     (stats >>= (\(nm,(t,ei_label_bytes)) ->
                   [nm ++ " :: " ++ showT t ++ ":"] ++
                   [showStatic ei_label_bytes]))
showStatic :: [Either (Name,Int) Int] -> String
showStatic ei_label_bytes = "[" ++
  
  (intercalate ", " $ map (\case Left (nm,len) -> nm ++ " : " ++ show len
                                 Right byte -> map intToDigit [byte `div` 16,
                                                               byte `mod` 16])
   ei_label_bytes)
  ++ "]"
  
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
    IRComment str -> ["--" ++ str]
    EVM_RETURN _ mem sto tsto ext ptr len ->
      [unwords ["evm_return",mem,sto,tsto,ext,ptr,len]]
    Switch _ tag numTags tag2block ->
      let tagblocks = M.toList tag2block
      in [unwords ["switch",tag,"(numTags "++show numTags++")","{"]] ++
         (do (tag,block) <- tagblocks
             [show tag ++ ":"] ++ indentBlock block) ++
         ["}"]
    ir -> error $ "Unsupported IR construct in prettyIR: " ++ show ir
indentBlock irs = map (' ':) (irs >>= prettyIR)

showLHS :: [(Name,IRT)] -> String
showLHS = intercalate ", " . map showNMT
showNMT (nm,irt) = nm ++ " : " ++ showIRT irt
showIRT = \case
  Mem -> "Mem"
  Sto -> "Sto"
  TSto -> "TSto"
  Ext -> "Ext"
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
      BEVM_RETURN mem sto tsto ext ptr len ->
        "RETURN":map showV [mem,sto,tsto,ext,ptr,len]
      BSwitch tag numTags tag2lab -> ["switch",showV tag,show numTags,
                                      show tag2lab]
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

-}
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
  A.Comment str -> "; " ++ str
prettyAsmLabel = \case
  LAnon n -> show $ "anon" ++ show n
  LNamed str -> str
