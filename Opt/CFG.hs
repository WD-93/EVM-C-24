{-# LANGUAGE LambdaCase #-}
module Opt.CFG where

import Core.RestrictedCore
import Const.Const (Serialized(..))

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S

--A first attempt at inferring the control-flow graph within and between C
--functions.
--That is made more difficult by the fact that all jumps are dynamic
--(to stack variables) rather than to static indices as in the prototype.
--The CFG must therefore be reconstructed by abstract interpretation, but the
--upside is that interprocedural inlining and tail-call optimization becomes
--possible.

{-
Core recap:
EVMC functions are polymorphic; before compilation to Core they are
instantiated and monomorphized. Each monomorphic function is compiled to a
function in the Structured IR. Structured retains structure such as if, while
and case, but makes ops such as mload explicit. Function calls are treated as
an op.
Conversion to Core decomposes each Structured functions into multiple basic
blocks and turns function calls into jumps with an explicit return continuation.
Jumps are annotated with their mode: return, call or interprocedural.

Abstract interpretation:
type AbState = [AbVar] --local stack; state vars not tracked
data AbVar = K n | f | jt | codeg | {fs,jts,codegs,mayBeK}
 {...} is an expr mentioning the given fs, jts and code globals
 If mayBeK is false, it must be one of them; if it is true it may also be
 some arbitrary k.
A call to k might be to any function of the right arity, or to an invalid
function. It should not liven any function, but call k S means all functions
of the right arity should have S added to their arg.
Track that S per arity, add to any newly discovered reachable function... or
add all at once later and iterate.

parent : coreF => cF
bbGraph : cF => coreF => BBInfo
cGraph : graph (node: f, edge: (f,args))?
 args : AbState
BBInfo:
 args : [AbState]
  --it's a list because each else branch also needs its state recorded
fspecs : f => args, ret, effect (returns | exits | may either)

Special entries:
 $trueMain => {$trueMain, $stop} --not a true C function
 arbitrary: args, ret

Algo:
Start from $trueMain, explore fun
It has a call edge to main.
Whenever a new function is called, give it spec top; iteratively expand the
function set referred to by top.
When exploring a function, track exec modality of BBs (maybe, definitely).
Definitely not => not included in the BB graph (yet).
Track call sites and callees.

callBB propagates through the BBs of a single C function, increasing BB args
and callee args.
It also depends on fspecs, whose ret should decrease.
Problem: the call graph must be built and used at the same time.

Instead of a global mem, use the mem var - then two branches of the program
needn't have the same labels in memory. Sto and tsto are analogous.
Ex use:
main() :=
 if cond
  then *ptr = f
  else *ptr()
 end
shouldn't liven f. That means a function may be mentioned but guaranteed to
never be called! They may be given value 0.

calldataload _;cd = {maybeK}
returndataload has no effect since mem is already maybeK.
-}

--Abstract variables; can represent both stack and state vars.
type Byte = Int
type Label = String --assumed to be a 2-byte label
data LabelType = Fun | JT | CodeG
  deriving (Eq,Ord,Read,Show)
--Integer should be cheaper than 32 Ints; I don't need to represent symbolic
--bytes here. It may be expensive for &, <<.
data AbVar = Bottom --no possible value
           | K Integer --a concrete 32B word value; 0 <= _ < 2^256
           | Exactly LabelType Label
           --Invariant to prevent overlap with Bottom and Exactly:
           --either mayBeK is True or the sets have >= 2 elems total
           | S {funs :: Set Label,
                jts :: Set Label,
                codeGs :: Set Label,
                mayBeK :: Bool
               }
  deriving (Eq,Ord,Read,Show)
--emptyS is an impossible value used as a template
emptyS :: AbVar
emptyS = S S.empty S.empty S.empty False
class Abstract a where
  bottom :: a
  lub :: a -> a -> a
instance Abstract AbVar where
  bottom = Bottom
  lub a b =
    --lub is commutative; we can therefore limit the cases considered
    --to a <= b by flipping the arguments otherwise.
    let (lo,hi) = if a <= b then (a,b) else (b,a)
    in if a == b
       then b
       else case lo of
              Bottom -> hi
              K n ->
                case hi of
                  K _ -> emptyS{mayBeK = True}
                  Exactly lt lab -> (singletonS lt lab){mayBeK = True}
                  s@S{} -> s{mayBeK = True}
              Exactly lt lab ->
                insertS lt lab $
                case hi of
                  Exactly lt' lab' ->
                    singletonS lt' lab'
                  s@S{} -> s
              _ -> unionS lo hi
insertS lt lab = unionS (singletonS lt lab)
singletonS lt lab =
  let s = S.singleton lab
  in case lt of
       Fun -> emptyS{funs = s}
       JT -> emptyS{jts = s}
       CodeG -> emptyS{codeGs = s}
--Precondition: both are S
unionS s1 s2 = S{funs = comb funs,
                 jts = comb jts,
                 codeGs = comb codeGs,
                 mayBeK = any mayBeK [s1,s2]
                }
  where comb f = S.union (f s1) (f s2)
  
--A BranchValue with AbVar instead of Var... TODO param?
--No need to record stk as an abvar, just whether it's present...?
--It would be nice to use abvars of the caller's stack; FW.
--Future opt: propagate guaranteed dead stk backward.
--(scope,Nothing,stk) is a more flexible goal: scope ++ _ satisfies it, even
--if you don't clean up.
--Revert and Return take Value arguments, but that's equivalent to
--(ws,False,ss).
type AbState = ([AbVar], Bool, [AbVar])
type AbValue = ([AbVar],[AbVar])

--TODO move concrete interp to another module
--With mem ops implemented by transforming the $mem absvar, op interpretation
--can be pure.
--Push ser has arity (0,0); the same mechanism can be used for checking the
--arity of other ops.
data BadInstr = BadArgArity {baaMnemonic :: String,
                             baaExpected :: (Int,Int),
                             baaActual :: (Int,Int)
                            }
              | BadMnemonic {baaMnemonic :: String}
              | MalformedSer Serialized
              | UnknownLabel Label
  deriving (Eq,Ord,Read,Show)
--That the lhs of the op matches the arity of the returned AbsValue is checked
--later.
interpOp :: Map Label LabelType -> PrimOp -> AbValue ->
  Either BadInstr AbValue
interpOp l2t (Push ser) = \case
  --If all bytes, K; if a single left-padded label, look up its
  --label type and the result is exactly that.
  --Otherwise it's a set of labels that mayBeK.
  --If serSizeof > serLength, that means it's right-padded.
  --That should not occur in a push...
  ([],[]) ->
    let Serialized {serLength = len,
                    serSizeof = sz,
                    serContent = cnt
                   } = ser
    in case () of
         _ | len /= sz -> Left $ MalformedSer ser
           | [Right (0,2,lab)] <- cnt ->
               ret1 <$> lab2var lab
           --Two traversals is simpler
           | all (\case Left _ -> True
                        _ -> False) cnt ->
               let bs = do Left bs <- cnt
                           bs
                   --TODO share this elegant bytes -> n definition
               in return $ ret1 $ K $ sum $ zipWith (*) (iterate (*256) 1) $
                  map fromIntegral $ reverse bs
           --(off,len) need not be (0,2), as a const may be
           --spread over several words. Ex: DT tags.
           | let -> do
             let labs = do Right (_,_,lab) <- cnt
                           return lab
             exs <- mapM lab2var labs
             --The K ensures mayBeK = True even if all labels are the same.
             return $ ret1 $ foldr lub bottom $ K 0 : exs
  (ws,ss) -> Left $ BadArgArity "push" (0,0) (length ws, length ss)
  where lab2var lab =
          case M.lookup lab l2t of
            Nothing -> Left $ UnknownLabel lab
            Just lt -> return $ Exactly lt lab
interpOp _l2t (Op op) = \(ws,ss) ->
  case M.lookup op opBehavior of
    Nothing -> Left $ BadMnemonic op
    Just (ar, f) ->
      let ar' = (length ws, length ss)
      in if ar /= ar'
         then Left $ BadArgArity op ar ar'
         else Right $ f (ws,ss)
--General patterns:
--Default concrete behavior
--Left and right-identities
--Absorbents and similar: _ << n>255 = 0, n*0 = 0, n>0 = 1...
--Rule composition:
--(a -> Maybe b) -> (a -> b) -> (a -> b)
--(a -> Maybe b) -> (a -> Maybe b) -> (a -> Maybe b)
--Functions can assume they're given args with the correct arity.
--General rule for pure ops:
--op(k1,k2) = concrete eval
--Remaining cases commutative
--op(k,f) = {funs: {f}, mayBeK}
--op(k,s) = s{mayBeK = True}
--op(f,g) = {funs: {f,g}, mayBeK}
--op(f,s) = insert f into funs, mayBeK = True
--op(f,s) = union sets, mayBeK = True
--mayBeK = False is preserved by lattice union on fs, gs
type OpFun = AbValue -> AbValue
opBehavior :: Map String ((Int,Int),OpFun)
opBehavior = M.fromList [
  --Branching and halting instructions and invalid are excluded
  --TODO give more detailed specs for sdiv, smod etc
  ("add", (,) (2,0) $ lrid 0 $ op2 (+))
  ,("mul",(,) (2,0) $ lrid 1 $ lrabs 0 $ op2 (*))
  ,("sub",(,) (2,0) $ rid 0 $ op2 (-))
  --div by 0 is 0...
  ,("div", (,) (2,0) $
     rule (\case ([a,K n],[])
                   | n == 1 -> Just $ ret1 a
                   | n == 0 -> Just $ ret1 $ K 0
                 _ -> Nothing) $ op2 div)
  ,("sdiv",(,) (2,0) $ dflt2)
  --I assume mod by 0 is also 0
  ,("mod", (,) (2,0) $ rule (\case ([a,K n],[])
                                     | n <= 1 -> Just $ ret1 $ K 0
                                   _ -> Nothing) $ op2 mod)
  ,("smod",(,) (2,0) $ dflt2)
  ,("addmod",(,) (3,0) $ dflt3)
  ,("mulmod",(,) (3,0) $ dflt3)
  ,("exp", (,) (2,0) $ op2 (^))
  ,("signextend", (,) (2,0) $ dflt2)
  --TODO add Bool to abstract domain
  ,("lt", (,) (2,0) $
     \case ([_, K 0],[]) -> ret1 $ K 0
           _ -> ret1 emptyS{mayBeK=True})
  ,("gt", (,) (2,0) $
     \case ([K 0, _],[]) -> ret1 $ K 0
           _ -> ret1 emptyS{mayBeK=True})
  ,("slt",(,) (2,0) $ bool2 $ error "todo")
  ,("sgt",(,) (2,0) $ bool2 $ error "todo")
  ,("eq",(,) (2,0) $ bool2 (==))
  ,("iszero", (,) (1,0) $
     \case ([K n],[]) ->
             ret1 $ K $ if n == 0
                        then 1
                        else 0
           _ -> ret1 emptyS{mayBeK=True})
  --f & 0x...0000 = 0
  --f & 0x...ffff = f
  ,("and",(,) (2,0) $ lrid (modulus - 1) $ op2 $ error "todo")
  ,("or", (,) (2,0) $ lrid 0 $ op2 $ error "todo")
  ]
--Notable rules:
--Because f is an exact but unknown 16b value:
--f & f, f | f = f
--f & 0xffff = f
--f == f = 1

--For binary funs with left and right identity
lrid :: Integer -> OpFun -> OpFun
lrid id f arg@([a,b],[]) =
  case (a,b) of
    (K n,_) | n == id -> ret1 b
    (_,K n) | n == id -> ret1 a
    _ -> f arg
rid id = rule (\case ([a, K n],[]) | n == id -> Just $ ret1 a
                     _ -> Nothing)
--For binary funs with an absorbent abs
lrabs abs f arg@([a,b],[]) =
  if K abs `elem` [a,b]
  then ret1 $ K abs
  else f arg
--Given a concrete implementation on integers, uses it if both args are
--K.
op2 :: (Integer -> Integer -> Integer) -> OpFun
op2 (+) ([a,b],[]) =
  ret1 $ case (a,b) of
           (K n, K m) -> K $ mod256 $ n + m
           _ -> lub a b
--Uses concrete implem if both args are K; False, True => 0,1.
--Returns an unknown bool by default.
bool2 :: (Integer -> Integer -> Bool) -> OpFun
bool2 (&) ([a,b],[]) =
  ret1 $ case (a,b) of
           (K n, K m) -> K $ if (n & m)
                             then 1
                             else 0
           _ -> emptyS{mayBeK = True}
dflt2 :: OpFun
dflt2 ([a,b],[]) = ret1 $ lub a b
dflt3 ([a,b,c],[]) = ret1 $ a `lub` b `lub` c
ret1 :: AbVar -> AbValue
ret1 v = ([v],[])
mod256 :: Integer -> Integer
mod256 n =
  let n' = n `mod` modulus
  in if n' < 0
     then n' + modulus
     else n'
modulus :: Integer
modulus = 2 ^ 256

--Extend a function with a rule that can override it when applicable
rule :: (a -> Maybe b) -> (a -> b) -> (a -> b)
rule mf f a =
  case mf a of
    Nothing -> f a
    Just b -> b

{-
AI algo:
Each Core basic block consists of n straight-line sections, where n is the
number of nested jumpis. They can be identified by (FunVar,Int), where the
initial SLS has index 0.
Each SLS has an input abstate (initially bottom for each var), output abstate
and branch edges. aiBB :: def -> abstate -> data and control flow edges.
Branch types:
Jumpi (may then, may else, branch dest)
 Dest is in practice constant
Jump:
 Call (branch abvar, ret dest)
 Return (branch abvar)
 Intraprocedural (branch dests)
Exits.

Track:
f <=> rets of call sites, f.args, f.ret
In f, sls:
call v,args,ret,scope:
 for g <- funs(v):
  if g has OK arity:
   g.args += args --adds g to workset
   add continues dataflow edge from sls to ret
 if v mayBeK:
  add mayBeK to ret's return value.
In f, sls:
 return v,retval:
  add control flow edge from sls to each g in v
  f.ret += retval
sls => f.
When sls1 in f reaches a new sls2 via IP, map bb2 => f.

AI of op graph:
Map each var to an abvar; map vars to consumers once.
Consumers are ops and branch params.
var += abvar =>
 extend state;
 if it changed, add consumers to workset.
It would be simpler to just rerun the SLS whenever the input changes;
it might even be cheaper.

Opt: mark mem param in revert(_,0) as dead. Replace return(_,0) with stop.

c -> f -> ret
c continues to ret iff f returns
Track f returns, queue conditions on it

v = s => v >= s
Rules as concurrent tasks, triggered by preconditions becoming true or
converging toward final conclusion.
Var changes trigger op tasks, which update vars. Is it optimal to run (var
changes, then all triggered op tasks) in a cycle?
-}
