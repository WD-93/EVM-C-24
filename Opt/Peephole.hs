{-# LANGUAGE LambdaCase #-}
module Opt.Peephole where

import Asm

import Data.Map (Map(..))
import qualified Data.Map as M

--This module is for optimizing generated assembly ([Asm]), not Core.
--The treegraph stack instruction scheduler has a problem: trees are currently
--run in a single arbitrary order, regardless of which is most efficient wrt
--the target stack.
--That means I get assembly like:
--push0
--push1 0x20
--swap1
--return
--which could trivially be optimized to push1 0x20, push0, return - eliminating
--the swap.
--For some reason the dead param elimination opt doesn't catch
-- $trueMain:
-- push 0
-- main:
-- pop
--either; I should opt that as well.
--General peephole opt is tricky, but if I restrict opt to runs of
--dup, push, swap, pop (potentially interspersed with labels) and peephole
--asm rather than bytecode it becomes trivial.
--Idea: any sequence is <- (dup | push | swap | pop)* where swaps and pops are
--"in range" (only swapping or popping words pushed by is) can be normalized
--to a series of dups and pushes.
--Algo: go through the asm sequentially; whenever a dup or push is
--encountered parse off the longest prefix of peepholable instructions,
--normalize, peephole the rest and then prepend the normalized instrs.
--Any placed labels encountered can be moved to the start of the normalized
--instrs; they're invalid jumpdests anyway.

--Tricky detail: the stack offset of dups need to be adjusted in the normalized
--code.
--Ex: push0, dup2, swap, pop - that should normalize to dup1.
--Should dups logically only be of words already on the stack? Yes: a push may
--be duplicated, but that logically corresponds to pushing a constant.
data LogicalWord = LPush Int Constant --may compile to a dup
                 | LDup Int --0-indexed, points into the preexisting stack
  deriving (Eq,Ord,Read,Show)
type Constant = [Asm] --Bytes and UseLabels, equivalent to Serialized.
--A normalized instruction sequence effect: a list of vars and constants are
--prepended to the stack. We also need to keep track of placed labels to
--prevent the linker from complaining.
type Normalized = (Int, [LogicalWord], [Label])
emptyNorm :: Normalized
emptyNorm = (0,[],[])
--Peepholable ops
data POp = PPush Int Constant
         | PDup Int --1-indexed, points into the current stack
         | PSwap Int --0-indexed > 0, points into the current stack
         | PPop
         | PPlaceLabel Label
  deriving (Eq,Ord,Read,Show)
tryApplyPOp :: Normalized -> POp -> Maybe Normalized
tryApplyPOp (height,ws,labs) = \case
  PPush len const -> Just (height+1,LPush len const : ws, labs)
  --Dup ixth elem of ws ++ LDup 0..
  PDup ix ->
    let dup'd = (ws ++ map LDup [0..]) !! ix
    in Just (height+1,dup'd:ws,labs)
  PSwap ix ->
    if ix >= height
    then Nothing
    else let a:prefix = take ix ws
             b:suffix = drop ix ws
         in Just (height,b:prefix ++ a:suffix,labs)
  PPop
    | height == 0 -> Nothing
    | let -> Just (height-1,tail ws,labs)
  PPlaceLabel lab -> Just (height,ws,lab:labs)
compileNormalized :: Normalized -> [Asm]
compileNormalized (height,lws,labs) =
  map PlaceLabel labs ++
  go 0 M.empty (reverse lws)
  where
    go :: Int -> --current stack height - original
          Map LogicalWord Int ->
          --tracks the offset off original stack where a preexisting
          --var or a new constant has been pushed; used to reduce dup depth
          --to avoid out of bounds error + replace pushes with dups.
          --Minimum: 1, higher offset => higher on the stack.
          [LogicalWord] ->
          [Asm]
    go height w2off = \case
      [] -> []
      
      lw:lws ->
        (case M.lookup lw w2off of
           --If the LWord is already on the new stack, duplicate it
           Just h -> [Opcode $ "dup"++show (height-h)]
           Nothing ->
            case lw of
              LPush len const ->
                (Opcode $ "push" ++ show len) : const
              LDup off -> [Opcode $ "dup" ++ show (off+height)]
        ) ++
        go (height+1) (M.insert lw height w2off) lws
{-
Algo: track accumulated stack and off.
For (dup, push), (swap, pop) in range, placelabel: simulate effect.
For other asm, flush stack, emit asm, continue.
-}
peephole :: [Asm] -> [Asm]
peephole = go emptyNorm
  where
    go :: Normalized -> [Asm] -> [Asm]
    go norm = \case
      [] -> compileNormalized norm
      asms@(asm:asms') ->
        case parsePOp asms of
          Just (pOp,asms'')
            | Just norm' <- tryApplyPOp norm pOp ->
              go norm' asms''
          --Flush the accumulated words, skip non-POp asm, continue
          _ -> compileNormalized norm ++ asm : peephole asms'

--Failure to parse a peepholable op is not a compiler error, so this returns
--a maybe.
--I treat Push and PushLabel as not peepholable, but that's fine
--since EVMC doesn't emit them. I also don't emit Dup or Swap.
parsePOp :: [Asm] -> Maybe (POp,[Asm])
parsePOp = \case
  [] -> Nothing
  asm : asms ->
    case asm of
      Opcode op 
        --push, dup, swap, pop, label
        | 'p':'u':'s':'h':strn <- op ->
            let len = read strn
                (const,asms') = parseImmArgs len asms
            in Just (PPush len const, asms')
        | 'd':'u':'p':strn <- op ->
            let n = read strn
            in Just (PDup n, asms)
        | 's':'w':'a':'p':strn <- op ->
            let n = read strn
            in Just (PSwap n, asms)
        | "pop" <- op -> Just (PPop,asms)
      PlaceLabel lab -> Just (PPlaceLabel lab, asms)
      _ -> Nothing
--Parses exactly n bytes of PUSH* immediate argument off asm.
--Accepts Bytes bs where |bs| <= m and UseLabel len lab where len <= m
--where m is the remaining number of bytes to parse;
--if anything else (including eof) is encountered then Codegen generated
--malformed assembly and parseImmArgs will throw an exception.
parseImmArgs :: Int -> [Asm] -> (Constant,[Asm])
parseImmArgs = go []
  where
    go accum n asms
      | n == 0 = (reverse accum, asms)
      | let = case asms of
                asm:asms' ->
                  case immLen asm of
                    Just len
                      | len > n -> error $ "Imm arg too long: " ++ show asm
                      | let -> go (asm:accum) (n-len) asms'
                    Nothing -> error $ "Not an imm arg: " ++ show asm
    immLen = \case
      Bytes bs -> Just $ length bs
      UseLabel _off len _ -> Just len
      _ -> Nothing
