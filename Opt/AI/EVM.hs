{-# LANGUAGE LambdaCase #-}
module Opt.AI.EVM (opBehavior,pushBehavior) where

import Opt.Semilattice
import Opt.AbVar
import Const.Const (Serialized(..))

import Data.Map (Map(..))
import qualified Data.Map as M

--Defines the abstract behavior of straight-line Core ops, i.e. the
--non-branching EVM ops less DUP*, SWAP*, POP.

type OpFun = AbValue -> AbValue
type AbValue = ([AbVar],[AbVar])
opBehavior :: Map String ((Int,Int), --arg arity
                          (Int,Int), --ret arity
                          OpFun --behavior
                         )
opBehavior = M.fromList [
  --(+) lrid 0
  ("add", arp 2 1 $ lrid 0 $ op21 (+))
  --(*) lrid 1, absorbent 0
  ,("mul", arp 2 1 $ lrid 1 $ absorbing 0 $ op21 (*))
  --(-) rid 0, f - f == 0
  ,("sub", arp 2 1 $ rid 0 $ ifEqual (const $ exactly 0) $ op21 (-))
  --f/f = 1, x/1 = x, x/0 = 0... 0/0 = 0?
  ,("div", arp 2 1 $ rid 1 $ ifEqual (const $ exactly 1) $
     rabsorbing 0 $ op21 div)
  ,("sdiv", arp 2 1 $ rid 1 $ ifEqual (const $ exactly 1) $
     rabsorbing 0 $ op21 $ onSigned div)
  --x mod ~1 = x, x mod (n<=1) = 0, fs mod n > 0xffff = f
  ,("mod", arp 2 1 $ rid (modulus-1) $ ifRLEQ1then0 $
     labelsUnaffectedIf (>=0xffff) $
     op21 mod)
  ,("smod", arp 2 1 $ ifRLEQ1then0 $
     labelsUnaffectedIf (\n -> n >= 0xffff && toSigned n >= 0) $
     op21 (\a b -> signum a * (abs a `mod` abs b)))
  --TODO add more properties
  ,("addmod", arp 3 1 $ op31 (\a b n -> (a + b) `mod` n))
  ,("mulmod", arp 3 1 $ op31 (\a b n -> (a * b) `mod` n))
  --(**) rid 1, x ** 0 = 1
  ,("exp", arp 2 1 $ rid 1 $ ifRThen (== exactly 0) (const $ exactly 1) $
     op21 (^))
  ,("signextend", arp 2 1 $ op21 $ error "todo")
  --f < f = 0, x < 0 = 0, fs < (n > 0xffff) = 1
  --Should bottom < bottom be bool?
  ,("lt", arp 2 1 $ ifEqual (const $ exactly 0) $ rabsorbing 0 $
          ifRThen (isKAnd (>0xffff)) (\abv ->
                                        if isLabel abv && abv /= bottom
                                        then exactly 0
                                        else bool) $
          op21bool (<))
  ,("gt", arp 2 1 $ op21bool (>))
  ,("slt", arp 2 1 $ op21bool $ onSigned (<))
  ,("sgt", arp 2 1 $ op21bool $ onSigned (>))
  --f == f = 1. TODO use bool == 1 = bool during symbolic simpl
  ,("eq", arp 2 1 $ ifEqual (const $ exactly 1) $ op21bool (==))
  --iszero fs = 0
  ,("iszero", arp 1 1 $
     \([w],[]) ->
       case () of
         _ | w == bottom -> ([bottom],[])
           | isLabel w && w /= bottom -> ([exactly 0],[])
           | Just k <- unexactly w ->
               ([exactly $ if k == 0 then 1 else 0],[])
           | let -> ([bool],[]))
  --f & 0x...ff = f
  --Need bitwise ops on Word256
  ,("and", arp 2 1 $ lrid (modulus-1) $ absorbing 0 $ op21 $ error "todo")
  ,("or", arp 2 1 $ lrid 0 $ absorbing (modulus-1) $ op21 $ error "todo")
  ,("xor", arp 2 1 $ lrid 0 $ ifEqual id $ op21 $ error "todo")
  ,("not", arp 1 1 $ op11 $ error "todo")
  --byte (n>31) _ = 0, byte _ 0 = 0
  ,("byte", arp 2 1 $ rabsorbing 0 $ ifRThen (isKAnd (>31)) (const $ exactly 0)
     $ op21 (\ix a ->
                (a `div` (2 ^ (248-8*ix))) `mod` 256))
  --shl 0 x = x; shl (n > 255) _ = 0
  ,("shl", arp 2 1 $ lid 0 $ rabsorbing 0 $
           ifLThen (isKAnd (> 255)) (const $ exactly 0) $
           op21 (\sh a -> a * 2 ^ sh))
  ,("shr", arp 2 1 $ lid 0 $ rabsorbing 0 $
           ifLThen (isKAnd (> 255)) (const $ exactly 0) $
           op21 (\sh a -> a `div` 2 ^ sh))
  --TODO verify
  ,("sar", arp 2 1 $ lid 0 $ rabsorbing 0 $
           ifLThen (isKAnd (> 255)) (const $ exactly 0) $
           op21 (\sh a -> toSigned a `div` 2 ^ sh))
  ,("keccak256", ar 2 1 1 0 $ \([ost,len],[mem]) ->
                  if bottom `elem` [ost,len,mem]
                  then ([bottom],[])
                  else ([bottom{possKs=All}],[]))
  --Arbitrary return value
  ,("address", ar 0 1 1 0 $ arb1)
  ,("balance",ar 1 1 1 0 $ arb1)
  ,("origin",ar 0 1 1 0 $ arb1)
  ,("caller",ar 0 1 1 0 $ arb1)
  ,("callvalue",ar 0 1 1 0 $ arb1)
  ,("calldataload",ar 1 1 1 0 $ arb1)
  ,("calldatasize",ar 0 1 1 0 $ arb1)
  ,("codesize",ar 0 1 1 0 $ arb1)
  --For all copies: if len == 0, return memory unchanged
  --Otherwise mem += source
  ,("codecopy", ar 3 2 0 1 $ error "todo")
  ,("gasprice", ar 0 1 1 0 $ arb1)
  ,("extcodecopy", ar 3 2 0 1 $ error "todo")
  ,("returndatasize", ar 0 1 1 0 $ arb1)
  ,("returndatacopy", ar 3 2 0 1 $ error "todo")
  ,("extcodehash", ar 1 1 1 0 $ arb1)
  ,("blockhash", ar 1 1 1 0 $ arb1)
  ,("coinbase", ar 0 1 1 0 $ arb1)
  ,("timestamp", ar 0 1 1 0 $ arb1)
  ,("number", ar 0 1 1 0 $ arb1)
  ,("prevrandao", ar 0 1 1 0 arb1)
  ,("gaslimit", ar 0 1 1 0 arb1)
  --chainid should usually be specialized...
  ,("chainid", ar 0 1 1 0 arb1)
  ,("selfbalance", ar 0 1 1 0 arb1)
  ,("basefee", ar 0 1 1 0 arb1)
  ,("blobhash", ar 1 1 1 0 arb1)
  ,("blobbasefee", ar 0 1 1 0 arb1)
  ,("mload", opload)
  --This should work because mem starts off 0 - if you write
  --a nonzero k to it it will be All, so mload won't see just
  --that k.
  ,("mstore", opstore)
  --f & 0xff is tainted by f
  ,("mstore8", opstore)
  ,("sload", opload)
  ,("sstore", opstore)
  ,("pc", ar 0 1 1 0 arb1)
  ,("msize", ar 0 1 1 0 arb1)
  ,("gas", ar 0 1 1 0 arb1)
  ,("tload", opload)
  ,("tstore", opstore)
  ,("mcopy", ar 3 2 0 1 $ error "todo")
  ,("log0",error "todo")
  ,("log1",error "todo")
  ,("log2",error "todo")
  ,("log3",error "todo")
  ,("log4",error "todo")
  ,("create",error "todo")
  --If retlen = 0, has no effect on memory
  --Modifies returndata, which is initially 0
  --Returns a Bool.
  --Q: does CREATE affect returndata?
  --A CALL or CREATE may reenter, modifying sto and tsto.
  --However, it can only do so by calling main... and so the
  --effect will be captured by looping back sto and tsto from
  --all exits to $trueMain.
  ,("call",error "todo")
  ,("callcode",error "todo")
  ,("delegatecall", error "todo")
  ,("staticcall", error "todo")
  --Boolean ops never return a label
  --TODO assume codecopy(to,codeG,n) mentions labs in codeG
  --TODO automate state var position calc using OpcodeInfo
  ]
  where ifRLEQ1then0 f =
          ifRThen (isLEQThan 1) (const $ exactly 0) f
        ifRThen pred f' f args@([w1,w2],[]) =
          if pred w2
          then ([f' w1],[])
          else f args
        ifLThen pred f' f args@([w1,w2],[]) =
          if pred w1
          then ([f' w2],[])
          else f args
        labelsUnaffectedIf pred f args@([w1,w2],[]) =
          if isKAnd pred w2 && isLabel w1
          then ([w1],[])
          else f args
        --abv is guaranteed to be > k
        isGreaterThan k = isKAnd (>k)
        --guaranteed to be <= k
        isLEQThan k = isKAnd (<=k)
        isKAnd pred abv
          | Just k <- unexactly abv = pred k
          | let = False
        --abv is either a label or bottom, but certainly not a k
        isLabel abv = possKs abv == None
        --TODO answer Q: should I propagate bottom here?
        arb1 (ws,ss)
          | bottom `elem` (ws++ss) = ([bottom],[])
          | let = ([bottom{possKs=All}],[])
        --For now, all mutable region loads and stores have the
        --same behavior.
        opload = ar 1 1 1 0 $ \([_off],[s]) -> ([s],[])
        opstore = ar 2 1 0 1 $ \([_off,w],[s]) -> ([],[w \/ s])
        --Tag the behavior with its arity; boilerplate
        ar :: Int -> Int -> Int -> Int -> OpFun -> ((Int,Int),(Int,Int),OpFun)
        ar a b c d f = ((a,b),(c,d),f)
        arp a b = ar a 0 b 0
--TODO use types to enforce arg and ret arity?
--Arg and ret arity is always a single digit, so no need for _

--The number of words; all word ops are modulo modulus
modulus = 2^256
--Positive signed numbers: 0..halfModulus-1
--Negative signed numbers: halfModulus..modulus-1
halfModulus = modulus `div` 2
--If negative, add modulus
toWord n =
  let n' = n `mod` modulus
  in n' + if n' < 0
          then modulus
          else 0
--Convert an unsigned word 0 <= n < modulus to a signed integer
toSigned n | n >= halfModulus = n - modulus
           | let = n
onSigned (*) a b = toSigned a * toSigned b

op31 :: (Integer -> Integer -> Integer -> Integer) -> OpFun
op31 f ([a,b,c],[])
  | bottom `elem` [a,b,c] = ([bottom],[])
  | Just [x,y,z] <- mapM unexactly [a,b,c] = ([exactly $ toWord $ f x y z],[])
  | let = ([(a \/ b \/ c){possKs=All}],[])
op21 :: (Integer -> Integer -> Integer) -> OpFun
op21 (+) ([w1,w2],[])
  | bottom `elem` [w1,w2] = ([bottom],[])
  | Just a <- unexactly w1,
    Just b <- unexactly w2 = ([exactly $ toWord $ a+b],[])
  | let = ([(w1 \/ w2){possKs = All}],[])
op11 :: (Integer -> Integer) -> OpFun
op11 f ([w],[])
  | w == bottom = ([w],[])
  | Just k <- unexactly w = ([exactly $ toWord $ f k],[])
  | let = ([w{possKs=All}],[])
--TODO answer q: is it safe for Boolean ops on bottom to return bool?
--That's safe but overapproximates: consider w1,w2 = bottom.
--If the result is bottom then they might increase to k1,k2, at which point
--you should be able to give a definite answer. If you've already returned
--bool it's too late.
op21bool (&) ([w1,w2],[])
  | bottom `elem` [w1,w2] = ([bottom],[])
  | Just a <- unexactly w1,
    Just b <- unexactly w2 = ([exactly $ if a & b then 1 else 0],[])
  | let = ([bool],[])
bool = bottom{possKs=All}
--Binary op left and right identity
lrid k = lid k . rid k
lid k f args@([w1,w2],[]) =
  if w1 == exactly k
  then ([w2],[])
  else f args
rid k f args@([w1,w2],[]) =
  if w2 == exactly k
  then ([w1],[])
  else f args
--Binary op left and right absorbing element
absorbing k f args@([w1,w2],[]) =
  if exactly k `elem` [w1,w2]
  then ([exactly k],[])
  else f args
--Used by div, sdiv
rabsorbing k f args@([w1,w2],[]) =
  if w2 == exactly k
  then ([w2],[])
  else f args
--TODO use for (-), (==), xor, and, or
--What I really want to check for is equality, but that can only be determined
--for labels and constants with the current AbVar repr.
--Since equal constants are already handled by the concrete implementation,
--I check only for equal labels.
ifEqual a2a f args@([w1,w2],[])
  | Just p1 <- unlabel w1, Just p2 <- unlabel w2,
    p1 == p2 = ([a2a w1],[])
  | let = f args
--Generic behavior: result = lub of inputs, possKs = All
             
--Push isn't part of the opBehavior map, but it makes sense to define its
--interpretation here.
--Given a map label => lt and a Serialized, returns the abstract value of
--Push ser. Uses a function rather than a Map to avoid having to M.union
--every time a push is interpreted.
--If ser is a single right-aligned label lab of len 2, look up its type and
--return {lt: {lab}}
--If ser is only bytes, returns {possKs = n}
--Otherwise, returns an abvar containing all mentioned labels with possKs = All.
--Errors with Left lab at the first unrecognized label lab.
pushBehavior :: (String -> Maybe LabelType) -> Serialized -> Either String AbVar
pushBehavior lab2lt Serialized{serContent = sc}
  | [Right (0,2,lab)] <- sc = mkLabel lab 
  | all (\case Left _ -> True
               _ -> False) sc = do
      let bs = do Left bs <- sc
                  bs
      return bottom{possKs = K $ sum $ zipWith (*) (iterate (*256) 1) $
                             map fromIntegral $ reverse bs
                   }
  | let = do
          labvars <- mapM mkLabel [lab | Right (_,_,lab) <- sc]
          return (foldr (\/) bottom labvars){possKs = All}
          where mkLabel lab = label <$> classify lab <*> return lab
                classify lab =
                  case lab2lt lab of
                    Nothing -> Left lab
                    Just lt -> return lt
