{-# LANGUAGE LambdaCase #-}
module Opt.AI.EVM (opBehavior,pushBehavior) where

import Opt.Semilattice
import Opt.AbVar
import Const.Const (Serialized(..))
--for ordering state vars correctly
import OpcodeInfo hiding (State) 
import qualified OpcodeInfo as OI
import Core.RestrictedCore (FunVar())

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.List (sort)
--For concrete bitwise ops; I still use Integer for K in order to represent
--small integers more compactly
import Data.WideWord.Word256 (Word256())
import qualified Data.WideWord.Word256 as W
import Data.Bits

--Defines the abstract behavior of straight-line Core ops, i.e. the
--non-branching EVM ops less DUP*, SWAP*, POP.

--Added the codeG => labels map to OpFun; it's used by codecopy and ignored
--by everything else, but handling that here avoids spreading EVM AI over
--several modules.
type OpFun = Map FunVar AbVar -> AbValue -> AbValue
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
  --signextend(b,f) for b > 1 will not affect labels
  --signextend(31,x) = x
  --signextend(b>31,x) = 0 or x?
  --What if x is larger than b expects? I'll assume those bytes are ignored.
  --TODO test with hardhat
  ,("signextend", arp 2 1 $ lid 31 $ op21 signextend)
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
     \_c2ls ([w],[]) ->
       case () of
         _ | w == bottom -> ([bottom],[])
           | isLabel w && w /= bottom -> ([exactly 0],[])
           | Just k <- unexactly w ->
               ([exactly $ if k == 0 then 1 else 0],[])
           | let -> ([bool],[]))
  --f & 0x...ff = f
  --Need bitwise ops on Word256
  ,("and", arp 2 1 $ lrid (modulus-1) $ absorbing 0 $ op21W (.&.))
  ,("or", arp 2 1 $ lrid 0 $ absorbing (modulus-1) $ op21W (.|.))
  ,("xor", arp 2 1 $ lrid 0 $ ifEqual id $ op21W xor)
  ,("not", arp 1 1 $ op11W complement)
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
  ,("keccak256", ar 2 1 1 0 $ \_c2ls ([ost,len],[mem]) ->
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
  ,("calldatacopy", copy "calldatacopy" Calldata)
  ,("codesize",ar 0 1 1 0 $ arb1)
  --For all copies: if len == 0, return memory unchanged
  --Otherwise mem += source
  ,("codecopy", ar 3 1 0 1 $ codecopy)
  ,("gasprice", ar 0 1 1 0 $ arb1)
  ,("extcodecopy", ar 4 2 0 1 $ extcodecopy)
  ,("returndatasize", ar 0 1 1 0 $ arb1)
  ,("returndatacopy", copy "returndatacopy" Returndata)
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
  --gas modifies Other in order to prevent reordering:
  ,("gas", ar 0 1 1 1 arb1) 
  ,("tload", opload)
  ,("tstore", opstore)
  ,("mcopy", copy "mcopy" Memory)
  --log* reads memory and modifies other
  ,("log0", logfun 0)
  ,("log1", logfun 1)
  ,("log2", logfun 2)
  ,("log3", logfun 3)
  ,("log4", logfun 4)
  --Like call*, create can modify contract-private state via reentrancy.
  --However, that needn't be simulated in the op itself - since AI is
  --monotonic, sto etc will already be the LUB of the effect of repeated CALLs
  --to main.
  --Minor opt: if code len is 0, it will not reenter.
  --Should I return bottom if any arg is bottom?
  ,("create", ar 3 5 1 4 $ \_ ([val,ost,len],[mem,sto,tsto,ext,other]) ->
                             ([bottom{possKs=All}], --0 or an addr
                              [sto,tsto,ext,other]))
  --If retlen = 0, doesn't write memory.
  --If arglen = 0, doesn't read memory.
  --Modifies returndata, which is initially 0.
  --Returns a Bool.
  --Q: does CREATE affect returndata? No.
  --A CALL or CREATE may reenter, modifying sto, tsto and other.
  --However, it can only do so by calling main... and so the
  --effect will be captured by looping back sto, tsto, other from
  --all exits to $trueMain.
  ,("call", ar 7 6 1 6 $ \_ (_,[mem,sto,tsto,rd,ext,other]) ->
                           ([mem{possKs=All}],
                            [bottom{possKs=All}, --May make arb changes to mem
                             sto,tsto,
                             bottom{possKs=All}, --Since it's initially 0
                             ext,other]))
  --callcode and delegatecall differ from call in that they can make arbitrary
  --changes to storage (and tstorage?).
  ,("callcode", ar 7 6 1 6 $ \_ (_,[mem,sto,tsto,rd,ext,other]) ->
                               ([bottom{possKs=All}],
                                [mem{possKs=All},
                                 sto{possKs=All},
                                 tsto{possKs=All},
                                 bottom{possKs=All}, --Since it's initially 0
                                 ext,other]))
  ,("delegatecall", ar 6 6 1 6 $ \_ (_,[mem,sto,tsto,rd,ext,other]) ->
                                   ([bottom{possKs=All}],
                                    [mem{possKs=All},
                                     sto{possKs=All},
                                     tsto{possKs=All},
                                     bottom{possKs=All},
                                     --Since it's initially 0
                                     ext,other]))
  ,("create2", ar 4 5 1 4 $ \_ ([val,ost,len,salt],
                                [mem,sto,tsto,ext,other]) ->
                              ([bottom{possKs=All}], --0 or an addr
                               [sto,tsto,ext,other]))
  --staticcall is like call except it transfers no value and the call may not
  --have any side effects (other than consuming gas).
  ,("staticcall", ar 6 2 1 2 $ \_ (_,[mem,rd]) ->
                                 ([bottom{possKs=All}],
                                  [mem{possKs=All},
                                   bottom{possKs=All}
                                  ]))
  --Boolean ops never return a label
  --TODO automate state var position calc using OpcodeInfo

  --The first straight-line op that isn't an EVM instruction!
  --emptyMem returns an empty memory map, and is used to pass a trivial
  --memory parameter to Revert when replacing infinite loops with reverts.
  --That's necessary because the original $mem may be dead in the loop.
  --It can also be used to pass an empty mem to revert(0,0) and return(0,0)
  --in place of $mem, allowing memory writes before them to be recognized as
  --dead by eliminating the false dependence on $mem.
  ,("emptyMem", emptyS)
  --Adding the rest (they're needed for eliminating false deps on dead ops
  --from dead branch params)
  ,("emptySto", emptyS)
  ,("emptyTSto", emptyS)
  ,("emptyCD", emptyS)
  ,("emptyRD", emptyS)
  ,("emptyExt", emptyS)
  ,("emptyOther", emptyS)
  ]
  where ifRLEQ1then0 f =
          ifRThen (isLEQThan 1) (const $ exactly 0) f
        ifRThen :: (AbVar -> Bool) -> (AbVar -> AbVar) -> OpFun -> OpFun
        ifRThen pred f' f c2ls args@([w1,w2],[]) =
          if pred w2
          then ([f' w1],[])
          else f c2ls args
        ifLThen :: (AbVar -> Bool) -> (AbVar -> AbVar) -> OpFun -> OpFun
        ifLThen pred f' f c2ls args@([w1,w2],[]) =
          if pred w1
          then ([f' w2],[])
          else f c2ls args
        labelsUnaffectedIf pred f c2ls args@([w1,w2],[]) =
          if isKAnd pred w2 && isLabel w1
          then ([w1],[])
          else f c2ls args
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
        arb1 _c2ls (ws,ss)
          | bottom `elem` (ws++ss) = ([bottom],[])
          | let = ([bottom{possKs=All}],[])
        --For now, all mutable region loads and stores have the
        --same behavior.
        opload = ar 1 1 1 0 $ \_c2ls ([_off],[s]) -> ([s],[])
        opstore = ar 2 1 0 1 $ \_c2ls ([_off,w],[s]) -> ([],[w \/ s])
        logfun topics = ar (2+topics) 2 0 1 $
                        \_c2ls (_,[mem,other]) -> ([],[other])
        --Tag the behavior with its arity; boilerplate
        ar :: Int -> Int -> Int -> Int -> OpFun -> ((Int,Int),(Int,Int),OpFun)
        ar a b c d f = ((a,b),(c,d),f)
        arp a b = ar a 0 b 0
        --Return a state var with abvar 0; its exact abvar doesn't really
        --matter because it's for emptyMem et al
        emptyS = ar 0 0 0 1 $ \_ _ -> ([],[exactly 0])

--TODO share logic with toSigned
signextend :: Integer -> Integer -> Integer
signextend b x
  | b > 31 = x --TODO test!
  | let = --truncate x to a b+1-byte number
          let bmod = 256 ^ (b+1)
              halfbmod = bmod `div` 2 --lowest negative number
              x' = x `mod` bmod
          in if x' >= bmod
             then x' - bmod
             else x'
              
--Copy behavior combinator; all copy variants load from memory to a given
--region. TODO take into account which codeG is being copied off in codecopy.
--Extcodecopy doesn't fit since it takes an additional address.
copy :: String -> OI.State -> ((Int,Int),(Int,Int),OpFun)
copy op r = ((3,if r == Memory then 1 else 2), --takes source region and memory
             (0,1), --updates memory
             (\_c2ls ([dst,ost,len],states) ->
                let mem = getSV op Memory states
                    dat = getSV op r states
                in if len == exactly 0 --if copied len is 0 it's a noop
                   then ([],[mem])
                   else ([],[mem \/ dat])
             )
            )
--OI.State doesn't have Code... that sort of makes sense since it's immutable,
--but will probably have to be changed once I add a more detailed region model.
--For now I assume code ~ {possKs=All}.
--That means any function or codeG mentioned in codeG initializers must be
--considered reachable in AI! TODO fix.
--If not,
--code jumptbl = Array(f1,f2,...fN);
--memtbl : Array N (A -> B)
--memory memtbl;
--main():= {copy(memtbl,&jumptbl,1); (memtbl!ix)(a)}
--could fail because f1..fN might be pruned.
--Adding codeG => labels handling:
--For each codeG in codeGs ost, union its abvar with mem.
--Precondition: any label mentioned in Core exists in the map...
codecopy c2ls ([dst,ost,len],[mem]) =
  if len == exactly 0
  then ([],[mem])
  else
    let cs = S.toList $ codeGs ost
        abvs = map (\c ->
                      case M.lookup c c2ls of
                        Just abv -> abv
                        _ -> error $ "Undefined label in Core: " ++ c) cs
    in ([],[foldr (\/) bottom{possKs=All} abvs])
--Ext is assumed to always be arbitrary; passing a label to another contract
--doesn't add it to ext. The ext state variable is solely used to order
--ops, e.g. an extcodecopy may not be commuted with a CALL.
extcodecopy _c2ls ([addr,dst,ost,len],svs) =
  let mem = getSV "extcodecopy" Memory svs
  in if len == exactly 0
     then ([],[mem])
     else ([],[mem{possKs=All}])
       
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
op31 f _c2ls ([a,b,c],[])
  | bottom `elem` [a,b,c] = ([bottom],[])
  | Just [x,y,z] <- mapM unexactly [a,b,c] = ([exactly $ toWord $ f x y z],[])
  | let = ([(a \/ b \/ c){possKs=All}],[])
op21 :: (Integer -> Integer -> Integer) -> OpFun
op21 (+) _c2ls ([w1,w2],[])
  | bottom `elem` [w1,w2] = ([bottom],[])
  | Just a <- unexactly w1,
    Just b <- unexactly w2 = ([exactly $ toWord $ a+b],[])
  | let = ([(w1 \/ w2){possKs = All}],[])
--Converts the Integers to Word256 and back
op21W :: (Word256 -> Word256 -> Word256) -> OpFun
op21W (+) = op21  $ \a b -> fromIntegral $ fromInteger a + fromInteger b
op11 :: (Integer -> Integer) -> OpFun
op11 f _c2ls ([w],[])
  | w == bottom = ([w],[])
  | Just k <- unexactly w = ([exactly $ toWord $ f k],[])
  | let = ([w{possKs=All}],[])
op11W :: (Word256 -> Word256) -> OpFun
op11W f = op11 (fromIntegral . f . fromInteger)
--TODO answer q: is it safe for Boolean ops on bottom to return bool?
--That's safe but overapproximates: consider w1,w2 = bottom.
--If the result is bottom then they might increase to k1,k2, at which point
--you should be able to give a definite answer. If you've already returned
--bool it's too late.
op21bool (&) _c2ls ([w1,w2],[])
  | bottom `elem` [w1,w2] = ([bottom],[])
  | Just a <- unexactly w1,
    Just b <- unexactly w2 = ([exactly $ if a & b then 1 else 0],[])
  | let = ([bool],[])
bool = bottom{possKs=All}
--Binary op left and right identity
lrid k = lid k . rid k
lid k f c2ls args@([w1,w2],[]) =
  if w1 == exactly k
  then ([w2],[])
  else f c2ls args
rid k f c2ls args@([w1,w2],[]) =
  if w2 == exactly k
  then ([w1],[])
  else f c2ls args
--Binary op left and right absorbing element
absorbing k f c2ls args@([w1,w2],[]) =
  if exactly k `elem` [w1,w2]
  then ([exactly k],[])
  else f c2ls args
--Used by div, sdiv
rabsorbing k f c2ls args@([w1,w2],[]) =
  if w2 == exactly k
  then ([w2],[])
  else f c2ls args
--TODO use for (-), (==), xor, and, or
--What I really want to check for is equality, but that can only be determined
--for labels and constants with the current AbVar repr.
--Since equal constants are already handled by the concrete implementation,
--I check only for equal labels.
ifEqual a2a f c2ls args@([w1,w2],[])
  | Just p1 <- unlabel w1, Just p2 <- unlabel w2,
    p1 == p2 = ([a2a w1],[])
  | let = f c2ls args
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

--When ops take and return multiple state vars, it's a hassle to remember in
--which order they're passed and returned.
--Fused.Monad.runOp defines the order by obtaining the states consumed/borrowed
--and produced from OpcodeInfo.hs.
--By duplicating that logic, I can query the argument state var list and
--produce a correctly ordered result state var list.
--That makes op AI defs robust to adding new state types which change the
--order.
--Aside: Opcodes distinguishes between consuming and borrowing only by whether
--a new var of the same type is returned. If I add ops which consume state but
--don't return a new version (e.g. free(ptr)), I'll need to update it.

--Query arg list. Errors if the opcode doesn't exist, a SV that isn't present
--is requested, or if the argument vars don't match the expected length.
getSV :: String   -> --the instr (determines the states passed/returned)
         OI.State -> --state type requested
         [AbVar]  -> --the argument vars
         AbVar       --the var of the given state type
getSV op s vs =
  let (consumes,_produces) = lookupEffect op
  in if length consumes /= length vs
     then error $ "Length mismatch in getSV " ++op++": " ++ show (consumes,vs)
     else case lookup s $ zip consumes vs of
            Nothing ->
              error $ "Requested nonexistent state in getSV "++op++": " ++
              show s
            Just v -> v
lookupEffect :: String -> ([OI.State],[OI.State])
lookupEffect mnemonic = 
  case M.lookup mnemonic opcodes of
    Nothing -> error $ "Bad instr " ++ mnemonic ++ " in lookupEffect!"
    Just oi ->
      case oiBehavior oi of
        Normal {obEffect = Effect consumes produces} ->
          (M.keys consumes, S.toList produces)
        other -> error $ "Not straight-line instr " ++ mnemonic ++
                 " in lookupEffect!"
--Returns the vars in the correct order.
--Errors if the state vars don't match what the instr expects.
retSVs :: String -> [(OI.State,AbVar)] -> [AbVar]
retSVs op svs =
  let (_consumes,produces) = lookupEffect op
      svs' = sort svs
  in case go produces svs' of
       Nothing -> error $ "Bad list in retSVs " ++ op ++ ": " ++
         show (op,produces,svs)
       Just vs -> vs
  where go [] [] = return []
        go (s:ss) ((s',v):svs)
          | s == s' = (v:) <$> go ss svs
        go _ _ = Nothing
          
