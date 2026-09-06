{-# LANGUAGE LambdaCase, TypeFamilies,
GeneralizedNewtypeDeriving, TypeOperators #-} --for monadic mocking
module Construct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
--For monadic implementation:
import Control.Monad.Writer
import Control.Monad (zipWithM, zipWithM_, forM, forM_)
import Data.Bits ((.&.),(.|.),complement) --for symbolic eval
import AST.DTs (roundedUpMod)
import Control.Monad.Except
--Testing:
import Test.QuickCheck hiding ((.&.),(.|.),output)
import qualified Data.Set as S
import Data.Char (intToDigit) --for Show sym byte and word instance
import Util (unsafePrint')

debugFlag = False
unsafePrint str = unsafePrint' debugFlag str

--A module for the logic of constructing and deconstructing values (Con and .).

construct :: Int -> --output size
             --Fields:
             [(Int, --offset from the right
               Int, --byte length
               [var]) --input words
             ] ->
             [[(var,Int)]] --each output word = disjunction of shifted inputs
             --positive => left-shift
construct outSz bss =
  expr outSz $ mapM_ go bss
  where go (off,sz,ws) = go' off sz $ reverse ws
        go' off sz = \case
          [] -> return ()
          w:ws -> do
            let wsz = min sz 32
            write off wsz w
            go' (off+wsz) (sz-wsz) ws
wsize :: Int -> Int
wsize sz = (sz `div` 32) + if sz `mod` 32 /= 0 then 1 else 0
--Produce the list of output words from the OutM monad
expr :: Int -> OutM var () -> [[(var,Int)]]
expr bytelen outm =
  let wlen = wsize bytelen
      ix2w = execState outm M.empty
  in [output ix ix2w | ix <- reverse [0..wlen-1]]

--With write and (+=) broken out of the where, we can elegantly state .field
--in terms of them!
write off wsz w = do
  let ix = off `div` 32
      m = off `mod` 32
  ix += (w,m)
  if m + wsz > 32
    then (ix+1) += (w,m-32)
    else return ()
(+=) :: Int -> (var,Int) -> OutM var ()
ix += wsh = modify (\m -> M.insert ix (wsh:output ix m) m)

output :: Int -> OutS var -> [(var,Int)]
output ix ix2w =
  case M.lookup ix ix2w of
    Nothing -> []
    Just w -> w
type OutS var = Map Int [(var,Int)]
--the array of output words being accumulated
--0 => the rightmost word on the stack
type OutM var = State (OutS var)

--Code-efficient dot:
--If there's garbage to the left of the field in its leftmost containing word,
--you need to shift or mask it out. Illust:
--[G bytes of garbage | 32-G bytes of field]
--The leftmost word of the input may only be included in the first two words
--of the output. If it is left-shifted by >=G (which can only occur in the
--second word), nothing more need be done. Otherwise, it can be left-shifted
--by G and then right-shifted to its intended position.
--However, that is not efficient if its shift was zero; then I'll mask.
--So only the top output word needs to be looked at; it's guaranteed to contain
--the top input word with some shift as the first element (for field size > 0).

--Problem: the leftmost word of the field may need to be masked.
--Solution: left-shift or mask it based on its shift and byte size.
--The relevant words (struct words which overlap with the field) are selected
--in Fused.
--Precondition: the field is in the range.
dot :: Int -> --right-offset modulo 32
       Int -> --field len
       [var] -> --the words in which the field is contained
       [[(var,Int)]]
       --each output word consists of the disjunction of shifted input words
dot off len ws =
  expr len $ go (-off)
  (len+off) --Why not len? Because we must count the bytes of the offset,
  --otherwise dot 3 2 ["w"] will write to word -1 but not 0
  $ reverse ws
  where go outOff {-the offset to write to-} len {-remaining bytes to write-} =
          \case
            [] -> return ()
            w:ws -> do
              let wsz = min len 32
              write outOff wsz w
              go (outOff+wsz) (len-wsz) ws

--TODO quickcheck that construct places fields at the right offsets and that
--dot fetches the relevant field.

-------------------------------------------------------------------------------
--New idea: a Construct class that can be overloaded to support both FFM
--and testing with a mock monad.
--It could be generalized to include control flow (calls, ifte...) in future.
--Vars in Fused need a type; Construct will be limited to allocating its own
--for each op. It can only handle Structured ops with no assignment and no
--side effects (since such ops take and return a list of state vars in
--addition to stack vars).
--Since EVM instructions only return 0 or 1 words, we restrict Construct to
--return 1 word. Why not 0 as well? Because those ops are side-effecting.
--The exception is pop, but it's not relevant to Core, in which the stack is
--abstract and doesn't need manipulation.
--This is a very simple monad; the only thing separating it from a monoid is
--sharing of vars.
--In practice ops also need to check whether the number of arguments is
--correct, but I won't track that here.
class Monad m => Construct m where
  type Var m
  type Op m
  --Ops that return one var
  op :: Op m ->
        [Var m] -> --args
        m (Var m)
  --Side-effecting ops that return nothing
  op0 :: Op m -> [Var m] -> m ()
  --Need to add constant to support shr. That strongly restricts vars to
  --representing integer-like things.
  --Alt: make shr, shl k ops.
  constant :: Integer -> m (Var m)
  --Debug comments:
  comment :: String  -> m ()
  --Branch on a var, performing either the th or el action based on whether
  --the var is zero. Both branches must return the same number of vars
  --(given by the Int parameter), otherwise an error should be thrown.
  --Bugfix: Construct has no facilities for managing the scope, so the cond
  --var in derefSto[uint2] was not in scope, triggering a SSA error.
  --The cond must be an m (Var m) instead of a Var m to ensure the Var is
  --created on the right side of the branch boundary.
  --Consequence: any vars used in the cond not already in scope when the
  --construct starts running must be in the cond action!
  ifte :: Int -> m (Var m) -> m [Var m] -> m [Var m] -> m [Var m]
  --derefSto also declares de facto locals before the ifte; they must be
  --available in the branches, so getScope and putScope must be moved into
  --Construct.
  getScope :: m [Var m]
  putScope :: [Var m] -> m ()

--Separating interpretations lets you simplify the respective monads.
--Interpretation 1: emit instructions, allocate new vars.
--Free monads could be used here.
--Problem: I pass in vars from the outside. How to represent them?
type V v = Either Int v
newtype Emit v a = Emit {unEmit :: StateT Int
                                   (Writer [EmitOp v]) a}
  deriving (Functor, Applicative, Monad)
data EmitOp v = V v := (String,[V v])
            | Push (V v) Integer
            | Comment String
  deriving (Eq,Ord,Read,Show)
runEmit :: Emit v a -> Int -> (a,[EmitOp v],Int)
runEmit (Emit sra) n =
  let ((a,s),w) = runWriter $ runStateT sra n
  in (a,w,s)
--For debugging:
printEmit :: Emit String [V String] -> IO ()
printEmit emit = do
  let (vs, ops, _) = runEmit emit 1
  mapM_ (putStrLn . showOp) ops
  printResult vs
    where showOp = \case
            v := (op, vs) ->
              unwords $ [showV v,"=",op] ++ map showV vs
            Push v n -> showV v ++ " = " ++ show n
            Comment str -> ";;" ++ str
          printResult vs = putStrLn $ unwords $ "Result:" : map showV vs
          showV = \case
            --Ambigous if you use v<n>...
            Left n -> "v"++show n
            Right str -> str
instance Construct (Emit v) where
  type Var (Emit v) = V v
  type Op (Emit v) = String
  op str vs = Emit $ do
    n <- get
    put (n+1)
    let v = Left n
    tell [v := (str,vs)]
    return v
  op0 = error "Not supported! (TODO modify instr type)"
  constant k = Emit $ do
    n <- get
    put (n+1)
    let v = Left n
    tell [Push v k]
    return v
  comment str = Emit $ tell [Comment str]
  ifte = error "Not supported (TODO modify Write type)"
  --Emit doesn't care about scope:
  getScope = return []
  putScope _ = return ()

emitM1 :: Emit String (V String)
emitM1 = do
  let [a,b,c] = map Right $ words "a b c"
  x <- op "+" [a,b]
  y <- op "+" [x,c]
  return y

--Symbolic eval interpretation; this is the one used for tests.
--It doesn't need any alloc machinery since "vars" are simply symbolic values.
newtype SymWord = SymWord [SymByte] --length = 32
  deriving Eq
data SymByte = K Int --0..255
             | X (String,Int) --(id,n)
             | OriginalMemByte Integer --represents memory before any writes
             | OriginalStoByte Integer --n = byte offset (32*slot+byte_index)
  deriving Eq
instance Show SymByte where
  show = \case
    K n -> map intToDigit [n `div` 16, n `mod` 16]
    X (str,n) -> str ++ "(" ++ show n ++ ")"
    OriginalMemByte n -> "m["++show n++"]"
    OriginalStoByte n -> "s["++show n++"]"
instance Show SymWord where
  show (SymWord bs) = "0x" ++ (bs >>= show)
--The ops relevant to struct construction and access.
--I don't need push since I'm evaluating rather than generating
--instructions; the constant in the instance can handle that.
--Needs to be String for compatibility with FFM...
type SymOp = String
wordK :: Integer -> SymWord
wordK n
  | n < 0 = wordK $
    let modulus = 2 ^ 256
    in (n `mod` modulus) + modulus
  | let = SymWord $ map (K . fromInteger) $ pad $ reverse $ take 32 $ go n
  where
    go :: Integer -> [Integer]
    go 0 = []
    go n = mod n 256 : go (n `div` 256)
    pad bs = replicate (32 - length bs) 0 ++ bs
newtype SymM a = SymM {unSymM :: StateT Regions (Except SymError) a}
  deriving (Functor, Applicative, Monad,
            MonadState Regions, MonadError SymError)
runSymM :: SymM a -> Regions -> Either SymError (a, Regions)
runSymM m r = runExcept $ runStateT (unSymM m) r
--Note that code, calldata and returndata don't need fields since they're
--immutable. Caveat: returndata can be modified by making a *CALL, but since
--I don't model calls that's not a problem.
--To avoid nondeterminism in the symbolic monad ("does px alias with py?"),
--I limit the regions to concrete addresses. Supporting symbolic addresses
--would also require me to make words as a whole symbolic in order to
--express x+k.
--The constant address limitation means I must quickcheck region accesses with
--random constant offsets rather than a single symbolic one in order to
--prevent coincidentally correct code due to constants.
--Note: while non-corrupt pointers are 16b, pointer offsetting can overflow
--that. Regions therefore need to be Word-addressed.
--A mapping for each byte is inefficient, but simple.
data Regions = Regions {
  symMemory :: Map Integer SymByte,
  symStorage :: Map Integer SymWord
  }
  deriving (Eq,Show)
--TODO add runSymM variant that passes nullRs and requires no change to it
--(for testing pure on-stack ops).
nullRs = Regions M.empty M.empty
data SymError = NotAByteConst SymWord
              | NotMul8 SymOp SymWord
              -- | BadArity SymOp [SymWord]
              | Can'tSimpBB SymOp SymByte SymByte
              | Can'tSimpNB SymOp Int SymByte
              | Can'tNOT SymByte
              | Can'tHandleSym String SymByte
              --Also thrown on bad arity:
              | UnrecognizedOp SymOp [SymWord]
              | UnrecognizedOp0 SymOp [SymWord]
              --ifte errors
              | InSpeculativeRun Bool SymError
              | BadNumVarsReturnedInBranch Bool Int [SymWord]
  deriving (Eq,Show)
instance Construct SymM where
  type Var SymM = SymWord
  type Op SymM = SymOp
  constant n = return $ wordK n
  op o [a,b] =
    case o of
      "byte" -> do
        --If ix > 31, return 0
        ix <- parseConst "byte" a
        if ix < 32
          then let SymWord bs = b
               in return $ SymWord $ replicate 31 (K 0) ++
                  [bs !! fromInteger ix]
          else constant 0
      --I'm starting to stretch the limits of what is convenient with this
      --simple monad...
      --For now support only for concrete values.
      "add" -> concreteWordOp2 "add" (+) a b
      "mul" -> concreteWordOp2 "mul" (*) a b
      "sub" -> concreteWordOp2 "sub" (-) a b
      "gt" -> concreteWordOp2 "gt" (\a b -> if a > b then 1 else 0) a b
      _ | o `elem` ["shr","shl"] -> do
            shBits <- parseConst (o++" first arg") a
            case () of
              _ | shBits >= 256 -> constant 0
                | (shBits `mod` 8) /= 0 -> do
                  --A non-byte shift can work on concrete values:
                  let n = 2 ^ shBits
                  bn <- parseConst (o++" second arg") b
                  constant $ case o of
                               "shr" -> bn `div` n
                               "shl" -> bn * n
                | let -> do
                    let shBytes = fromInteger $ shBits `div` 8
                        zeroes = replicate shBytes $ K 0
                        SymWord bs = b
                    return $ SymWord $
                      case o of
                        "shr" -> take 32 $ zeroes ++ bs
                        "shl" -> reverse $ take 32 $ zeroes ++ reverse bs
          --While partial-byte shift is possible in the EVM, I don't use
          --it; just error if a % 8 /= 0.
          --If any byte above the lowest isn't K 0, error.
          --Otherwise shift by a/8 bytes.
        --Bitwise ops
        | let -> do
            let SymWord as = a
                SymWord bs = b
            SymWord <$> zipWithM (apply o) as bs
  op "mload" [a] = do
    off <- parseConst "mload" a
    rs <- get
    let fetch ix =
          case M.lookup ix $ symMemory rs of
            Just symB -> symB
            Nothing -> OriginalMemByte ix
    return $ SymWord [fetch ix | ix <- [off..off+31]]
  op "sload" [a] = do
    off <- parseConst "sload" a
    rs <- get
    return $ case M.lookup off $ symStorage rs of
               Just symW -> symW
               Nothing -> SymWord [OriginalStoByte ix
                                  | ix <- [32*off..32*off+31]]
  op "not" [SymWord bs] = SymWord <$> mapM symNot bs
  op o ws = throwError $ UnrecognizedOp o ws
  op0 "mstore" [a,b] = do
        off <- parseConst "mstore" a
        let SymWord bs = b
        zipWithM_ writeMemByte [off..] bs
  op0 "mstore8" [a, SymWord bs] = do
    off <- parseConst "mstore8" a
    writeMemByte off $ last bs
  op0 "sstore" [a,b] = do
    off <- parseConst "sstore" a
    rs <- get
    put rs{symStorage = M.insert off b $ symStorage rs}
  op0 "mcopy" [vto,vfrom,vlen] = do
    ws <- mapM (parseConst "mcopy") [vto,vfrom,vlen]
    let [to,from,len] = ws
    bs <- mapM loadMemByte [from..from+len-1]
    zipWithM_ writeMemByte [to..] bs
  op0 o ws = throwError $ UnrecognizedOp0 o ws
  comment _ = return ()
  --IC the bug... I can't afford to check whether the unexecuted branch
  --returns the right number of words because it may throw a symbolic error.
  --That's because executing the wrong branch in storage ptr write causes
  --a value to be or'd with old storage, which can't be represented in
  --SymByte (yet).
  ifte n cond th el = do
    --For now we only allow branching on concrete values; doing so on
    --symbolic values would require adding [(CondTrace,_)] to the transformer
    --stack.
    k <- cond >>= parseConst "ifte"
    if k > 0
      then th
      else el
  --SymM doesn't care about scope:
  getScope = return []
  putScope _ = return ()
--Used to test both branches of ifte in SymM
--Errors if the speculative action errors, or if it returns the wrong number
--of words.
speculativeRun ::
  Bool -> --true or false branch for error reporting
  Int -> --expected num vars returned
  SymM [SymWord] ->  --action
  SymM ([SymWord],Regions)
speculativeRun b n symm = do
  s <- get
  case runSymM symm s of
    Left err -> throwError $ InSpeculativeRun b err
    Right (vs,s')
      | length vs == n -> return (vs,s')
      | let -> throwError $ BadNumVarsReturnedInBranch b n vs
      
--Writes a symbolic byte to the given offset in memory.
--The default value at offset off is OriginalMemByte off; if that is written
--delete the mapping instead.
writeMemByte :: Integer -> SymByte -> SymM ()
writeMemByte off b =
  modify (\rs->rs{symMemory = (if b == OriginalMemByte off
                                then M.delete off
                                else M.insert off b) $
                              symMemory rs
                 }
         )
--TODO standardize names to get and set?
loadMemByte :: Integer -> SymM SymByte
loadMemByte ix = gets fetch
  where fetch rs =
          case M.lookup ix $ symMemory rs of
            Just symB -> symB
            Nothing -> OriginalMemByte ix
--Inefficient... if I want fast symbolic eval in future need to make byte-level
--symbolic repr optional.
concreteWordOp2 :: String ->
                   (Integer -> Integer -> Integer) ->
                   SymWord -> SymWord ->
                   SymM SymWord
concreteWordOp2 op f a b = do
  an <- parseConst op a
  bn <- parseConst op b
  return $ wordK $ f an bn `mod` (2 ^ 256)

--Parses a constant 
--TODO use constraints on m instead of fixed type...
parseConst :: String -> SymWord -> SymM Integer
parseConst op (SymWord symBs) = do
  bs <- forM symBs (\case K n -> return n
                          sym -> throwError $ Can'tHandleSym op sym)
  return $ go 1 $ reverse bs
    where go mul = \case
            [] -> 0
            b:bs -> (mul * fromIntegral b) + go (mul*256) bs
          
--I just need to test bitwise not on constants for now, no need to extend
--the symbolic byte repr.
symNot :: SymByte -> SymM SymByte
symNot = \case
  K n -> return $ K $ complement n .&. 0xff
  b -> throwError $ Can'tNOT b
  
apply :: SymOp -> SymByte -> SymByte -> SymM SymByte
apply o (K a) (K b) =
  return $ K $ appK o a b
apply "and" (K n) x = simpAnd n x
apply "and" x (K n) = simpAnd n x
apply "or" (K n) x = simpOr n x
apply "or" x (K n) = simpOr n x
apply o a b
  | a == b = return a
  | let = throwError $ Can'tSimpBB o a b
simpAnd :: Int -> SymByte -> SymM SymByte
simpAnd n x =
  case n of
    0 -> return $ K 0
    255 -> return x
    _ -> throwError $ Can'tSimpNB "and" n x
simpOr :: Int -> SymByte -> SymM SymByte
simpOr n x =
  case n of
    0 -> return x
    255 -> return $ K 255
    _ -> throwError $ Can'tSimpNB "or" n x
appK :: String -> Int -> Int -> Int
appK o a b =
  case o of
    "and" -> a .&. b
    "or" -> a .|. b
    _ -> error $ "Unexpected op in appK: " ++ o
  
--Errors if not byte constant.
parseByte :: SymWord -> SymM Int
parseByte w@(SymWord (b:bs)) = go b bs
  where go (K n) [] = return n
        go (K 0) (b:bs) = go b bs
        go _ _ = throwError $ NotAByteConst w

--------------------------Monadic dot------------------------------------------
--What info does dot need for efficiency?
--Dot and construct both have the property that input bytes don't interact,
--they're rearranged. That could be called dot-like.
--Laws: adjacent slices concatenated together => one larger slice.
--Optimizing repeated dot and construct operations is promising...
--Repeated dot-like operations result in words of form [0x00 | input byte].
--An input word may have zero-padding both to the left and right of the
--relevant slice.
--Full info: which bytes are guaranteed to be zero in a type.
--For now emit unoptimized instrs, using only struct byte size (which we need
--to compute the offset into the stack words).
--Copying implem from Fused.getDot, using dot for now; refine later.
mdot :: (Construct m, Op m ~ String) =>
  Integer -> --struct sizeof, precondition: 0 <= it <= |vs|*32
  Integer -> --field byte offset from the left, 0 <= it <= sizeof
  Integer -> --field byte length
  [Var m] -> --struct words
  m [Var m]
mdot _ _ 0 _ = return []
--Special case encountered by newtypes, .tagBool etc:
mdot szStruct _ szField vs | szStruct == szField = return vs
mdot szStruct off szField vs = do
  let leftPad = (szStruct `roundedUpMod` 32) - szStruct
      stackOff = leftPad + off
      startIx = stackOff `div` 32
      endIx = (stackOff + szField - 1) `div` 32
      relVs = take (fromInteger $ endIx-startIx+1) $
              drop (fromInteger startIx) vs
      --right-offset mod 32
      rightOff = (szStruct - off - szField) `mod` 32
  --If the field size is 1, we use BYTE instead.
  --Index 0 => the MSB.
  if szField == 1
    then do
    let [relV] = relVs
    ix <- constant (31-rightOff)
    fld <- op "byte" [ix,relV]
    return [fld]
    else do
    --Output words = disjunction (input << +-k)
    let wshifts = dot (fromIntegral rightOff)
                  (fromIntegral szField) relVs
    let whd:wtl = wshifts
        (top,sh):wrest = whd
        garb = stackOff `mod` 32
    vtop <-
      if garb == 0
      then top <<< sh --no need to shift out garbage
      else if sh /= 0
           then (top <<< garb) >>= (<<< (fromIntegral sh - garb))
                --shift out garbage, then shift back
           else maskBytes (32-garb) top
                --can't use shift trick, must use code-intensive
                --and 0xff... instead.
    vrest <- forM wrest (\(v,sh) -> v <<< sh)
    vhd <- disjunction $ vtop:vrest
    vtl <- (forM wtl (\wshs ->
                        forM wshs (\(w,sh) -> w <<< sh)))
           >>= mapM disjunction
    return $ vhd : vtl

(<<<) :: (Construct m, Op m ~ String, Integral k) =>
  Var m -> k -> m (Var m)
v <<< k
  | k < -31 = constant 0
  | k < 0 = do
      kv <- constant $ negate $ fromIntegral k * 8
      op "shr" [kv,v]
  | k == 0 = return v
  | k < 32 = do
      kv <- constant $ fromIntegral k * 8
      op "shl" [kv,v]
  | let = constant 0
            
maskBytes :: (Construct m, Op m ~ String) => Integer -> Var m -> m (Var m)
maskBytes k v
  | k < 0 = constant 0
  | k >= 32 = return v
  | let = do
          vk <- constant (256^k-1)
          op2 "and" vk v

--Ors the given vars together
disjunction :: (Construct m, Op m ~ String) => [Var m] -> m (Var m)
disjunction = foldlOp "or" (constant 0)
--Where do I use conjunction? That determines whether the identity should be
--1 or ~0.
conjunction :: (Construct m, Op m ~ String) => [Var m] -> m (Var m)
conjunction = foldlOp "and" (constant 1)
--Combines the given words with a primop; returns a default expr if the list
--is empty.
--Can be used for conjunction, disjunction, sum...
foldlOp :: Construct m => Op m -> m (Var m) -> [Var m] -> m (Var m)
foldlOp op dflt = \case
  [] -> dflt
  v:vs -> go v vs
    where go v = \case
            [] -> return v
            v':vs -> do
              w <- go v' vs
              op2 op v w

op2 :: Construct m => Op m -> Var m -> Var m -> m (Var m)
op2 o a b = op o [a,b]

addK :: (Construct m, Op m ~ String) => Integer -> Var m -> m (Var m)
addK k v
  | k == 0 = return v
  |let = opE2 "add" (constant k) (return v)

--Correctness property: given a struct
--{garbLeft: a bytes, field: b bytes, garbRight: c bytes},
--dot returns the field.
prop_mdot_correct :: NonNegative Int ->
                     NonNegative Int ->
                     NonNegative Int ->
                     Bool
prop_mdot_correct (NonNegative a) (NonNegative b) (NonNegative c) =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      aBs = toBs "a" a
      fieldBs = toBs "field" b
      bBs = toBs "b" c
      struct = aBs ++ fieldBs ++ bBs
      structWs = wordSplit struct
  in case runSymM (mdot (fromIntegral $ a+b+c)
                   (fromIntegral a)
                   (fromIntegral b)
                   structWs) nullRs of
       Right (fld,_) ->
         let fieldBs' = unWordSplit fld
         in if fieldBs' /= fieldBs
            then error $ "Mismatch: " ++ show fieldBs' ++ " " ++ show fieldBs
            else True
       Left err -> error $ "Sym eval error: " ++ show err

--Converts byte-level to word-level on-stack repr.
--Left-pad with zeroes, then split into groups of 32 bytes.
wordSplit :: [SymByte] -> [SymWord]
wordSplit bs =
  let len = length bs
      stackLen = len `roundedUpMod` 32
      paddedBs = replicate (stackLen - len) (K 0) ++ bs
  in map SymWord $ group32 paddedBs
  where group32 = \case
          [] -> []
          bs -> take 32 bs : group32 (drop 32 bs)
--Converts back to the byte-level repr. Concatenate bytes, then drop leading
--zeroes.
unWordSplit :: [SymWord] -> [SymByte]
unWordSplit ws = dropZeroes $ ws >>= (\(SymWord bs) -> bs)
  where dropZeroes = \case
          [] -> []
          K 0 : bs -> dropZeroes bs
          bs -> bs

mconstruct :: (Construct m, Op m ~ String) => 
              Int -> --Output size
              --Fields:
              --Note: they should be passed in descending order of right-offset
              [(Int,     --offset from the right
                Int,     --byte length
                [Var m]) --input words
              ] ->
              m [Var m]
mconstruct szStruct fields = do
  let vshss = construct szStruct fields
  forM vshss (\vshs -> do
                 vs <- mapM (uncurry (<<<)) vshs
                 disjunction vs)

--For ns, let field_i = f<i> 1..ns_i
--Offsets = sum of previous sizes (counted from right)
--Byte length = ns_i
--Input words = word-split field_i
prop_construct_correct :: [NonNegative Int] -> Bool
prop_construct_correct nonNegNs =
  let ns = map (\(NonNegative n) -> n) nonNegNs
      fs = reverse $ go 0 1 ns
      wfs = map (\(off,len,bs) -> (off,len,wordSplit bs)) fs
      --The byte repr of the value that should result:
      target = fs >>= (\(_,_,bs) -> bs)
  in case runSymM (mconstruct (sum ns) wfs) nullRs of
       Right (ws,_) ->
         let actual = unWordSplit ws
         in if actual == target
            then True
            else error $ unlines [
           "Mismatch: " ++ show actual ++ " " ++ show target,
           "fs: " ++ show fs,
           "wfs: " ++ show wfs
           ]
       Left err -> error $ "Error: " ++ show err
  where go off i = \case
          [] -> []
          n:ns -> (off, n, toBs ("f"++show i) n) : go (off+n) (i+1) ns
        toBs nm len = [X (nm,n) | n <- [1..len]]

--Next: array get, field and array set on stack variables.
--TODO replace fields and indices in EvaluatedPat with offsets?
--Then .a.b could be merged.(Arr m (Arr n t))!a!b ~ !((a*k)+b) on an
--Arr (m*n) t.
--For now, support only array get and set for >2-word arrays.
--Indexing out of range is UB.

--struct' = struct{field=v}
--Algo:
--Select the words that overlap with the field:
--(unchangedLeft,overlapping,ucRight) = struct
--Zero the field bytes in overlapping:
--overlapping' = overlapping & 0x...
--Use construct to left-shift v by right-offset % 32:
--v' = v << roff % 32
--overlapping'' = overlapping' | v'
--return (unchangedLeft,overlapping'',ucRight)

--Note when masking, the field words to mask consist of either:
--One word: ff00ff
--Multiple words: [ff00], 00*, [00ff]. The 00 patterns are words where the whole
--word is taken up by the field, so instead of masking and or'ing you can
--simply replace the old word with v's word.
msetDot :: (Construct m, Op m ~ String) =>
           Integer -> --struct sizeof
           Integer -> --field byte offset from the left
           Integer -> --field byte length
           [Var m] -> --old struct words
           [Var m] -> --new field words
           m [Var m]  --new struct words
msetDot szStruct off szField struct field
  | szField == 0 = return struct
  | let = do
          --Ex: szStruct = 3, off = 0, szField = 1: 2
          let rightOff = szStruct - off - szField
              sh = rightOff `mod` 32
          --Does mconstruct handle sh == 0 gracefully? Might as well skip
          --anyway.
          --Note the zero should be optimized away here.
          comment "Shifting the field:"
          field' <- if sh == 0
                    then return field
                    else do
            z <- constant 0
            mconstruct (fromInteger $ szField+sh)
                      [(fromInteger sh,
                        fromInteger szField,
                        field),
                       (0, fromInteger sh, [z])
                      ]
          comment "Merging with old struct:"
          let stackOff = (szStruct `roundedUpMod` 32) - szStruct + off
              masks = [mkDotMask stackOff szField (fromIntegral i)
                      | i <- [0..length struct]]
          go struct masks field'
            where
              --All done:
              go ss _ [] = return ss
              --Haven't reached field yet:
              go (s:ss) (Oxff:ms) fs = (s:) <$> go ss ms fs
              --Combining:
              go (s:ss) (m:ms) (f:fs) = do
                s' <- applyDotMask s f m
                (s':) <$> go ss ms fs

--Indicates how the struct word is to be combined with the shifted field word.
data SetDotMask = Oxff --no overlap with field
                | Ox00 --full overlap with field
                | Oxff00 Integer --field in the n lowest bytes
                | Ox00ff Integer --field in the 32-n highest bytes
                | Oxff00ff Integer Integer --field in middle (right-off, len)
  deriving (Eq,Ord,Read,Show)
--How does the field overlap with the word?
--Precondition: szF > 0
mkDotMask :: Integer -> Integer -> Integer -> SetDotMask
mkDotMask off szF i =
  let wOff = 32*i
      (startF,endF) = (off,off+szF-1)
      (startW,endW) = (wOff,wOff+31)
  in case () of
       _ | startW > endF || endW < startF -> Oxff
         | startF <= startW, endW <= endF -> Ox00
         | startF > startW, startF <= endW, endF >= endW  ->
           Oxff00 $ 32 - (startF - startW)
         | startF <= startW, endF >= startW, endF < endW ->
           Ox00ff $ 32 - (endF - startW + 1)
         | let -> Oxff00ff (endW - endF) (endF - startF + 1)
--Given overlap info, combine the shifted field word with the original struct
--word.
--TODO opt: make use of padding bytes in struct. If the result of byte i of
--old & mask is guaranteed to be 0, byte i of mask can be 0.
--For {a:Bool,b:Bool}.a=vs, the mask can be 0xff rather than ff00ff. and 0xff
--can in turn be replaced with byte 31 (which may be more code-efficient if
--you have multiple uses of 31).
applyDotMask :: (Construct m, Op m ~ String) =>
  Var m -> Var m -> SetDotMask -> m (Var m)
applyDotMask sW fW = \case
  Oxff -> error "!?" --return sW
  Ox00 -> return fW
  --We do a little golfing... todo do more or constant expand in opt phase
  sdm -> do
    m <- case sdm of
           Oxff00 n -> do
             comment "Mask: Oxff00"
             m' <- constant $ 256 ^ n - 1
             op "not" [m']
           Ox00ff n -> do
             comment "Mask: Ox00ff"
             comment $ "Bytes: " ++ show n
             constant $ 256 ^ n - 1
           Oxff00ff rightOff len -> do
             comment "Mask: Oxff00ff"
             comment $ "Field len: " ++ show len
             ox00ff <- constant $ 256 ^ len - 1
             sh <- constant $ rightOff * 8
             ox00ff00 <- op "shl" [sh,ox00ff]
             op "not" [ox00ff00]     
    sW' <- op "and" [m,sW]
    op "or" [sW',fW]

--Correctness property: given a struct
--{garbLeft: a bytes, field: b bytes, garbRight: c bytes} and new
--field value: b bytes, msetDot returns
--{garbLeft, new field value, garbRight}
prop_msetDot_correct :: NonNegative Int ->
                        NonNegative Int ->
                        NonNegative Int ->
                        Bool
prop_msetDot_correct (NonNegative a) (NonNegative b) (NonNegative c) =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      aBs = toBs "a" a
      fieldBs = toBs "field" b
      bBs = toBs "b" c
      oldStruct = aBs ++ fieldBs ++ bBs
      oldStructWs = wordSplit oldStruct
      newFieldBs = toBs "new" b
      newFieldWs = wordSplit newFieldBs
      newStruct = aBs ++ newFieldBs ++ bBs
      newStructWs = wordSplit newStruct
  in case runSymM (msetDot (fromIntegral $ a+b+c)
                   (fromIntegral a)
                   (fromIntegral b)
                   oldStructWs newFieldWs) nullRs of
       Right (struct',_) ->
         let struct'Bs = unWordSplit struct'
         in if struct'Bs /= newStruct
            then error $ "Mismatch: " ++ show struct'Bs ++ " " ++ show newStruct
            else True
       Left err -> error $ "Sym eval error: " ++ show err

--Get and set an element of a one-word array on stack.
--Supporting multi-word array index on stack would require a jump table.
--Edge case: what if you index a 0-length array? Just return null; that's
--handled in Fused. Note it should be UB; returning null is just a convenient
--default.
mgetBang :: (Construct m, Op m ~ String) =>
  Integer -> --the array len (needed for right-shift, > 0)
  Integer -> --the byte size of array elems (> 0)
  Var m ->   --the array
  Var m ->   --the index : Short
  m (Var m)  --the result (always one word)
mgetBang arrlen sza arr ix
  | sza == 1 =
    if arrlen == 32
    then op "byte" [ix,arr]
    else do
      --The first byte is at offset 32-arrlen
      k <- constant $ 32 - arrlen
      ix' <- op "add" [k,ix]
      op "byte" [ix',arr]
  | let = do
          --Shift and mask; the lowest index is leftmost
          --We shl the requested element as far left as possible,
          --then back to offset 0
          k <- constant $ sza * 8
          sh <- do
            let garb = 32 - arrlen * sza
            if garb == 0
              then op "mul" [k,ix]
              else do
              sh' <- op "mul" [k,ix]
              p <- constant $ garb * 8
              op "add" [p,sh']
          arr' <- op "shl" [sh,arr]
          rsh <- constant $ 256 - sza * 8
          op "shr" [rsh,arr']

{-Algo(arr,ix,elem):
sh = right-offset of arr[ix]: sza*8*(arrlen-1) - sza*8*ix
m = ~(mask sza << sh)
return arr & m | elem << sh
-}
msetBang :: (Construct m, Op m ~ String) =>
  Integer -> --the array len (needed for right-shift, > 0)
  Integer -> --the byte size of array elems (> 0)
  Var m ->   --the array
  Var m ->   --the index : Short
  Var m ->   --the element to assign to the index
  m (Var m)  --the updated array (always one word)
msetBang arrlen sza arr ix elem = do
  sh <- opE2 "sub" (constant $ sza*8*(arrlen-1)) $
        opE2 "mul" (constant $ sza*8) (return ix)
  m <- opE1 "not" $ opE2 "shl" (return sh) $ constant $ 256 ^ sza - 1
  opE2 "or" (opE2 "shl" (return sh) (return elem)) $
    opE2 "and" (return m) (return arr)
--Finally defining combinators for defining ops in an expr-like manner, a la
--Ecomp
opE1 :: Construct m => Op m -> m (Var m) -> m (Var m)
opE1 o e = do
  v <- e
  op o [v]
--Subexpr eval in textual order; treegraph stack scheduling should optimize
--that for pure ops.
opE2 :: Construct m => Op m -> m (Var m) -> m (Var m) -> m (Var m)
opE2 o e1 e2 = do
  a <- e1
  b <- e2
  op o [a,b]

--mgetBang's correctness can actually be exhaustively checked since array
--size is bounded.
test_mgetBang_correct :: Either String ()
test_mgetBang_correct =
  mapM_ test [(arrlen,sza,ix)
             | sza <- [1..32],
               arrlen <- [1..32 `div` sza],
               ix <- [0..arrlen-1]
             ]
  where
    test :: (Integer, Integer, Integer) -> Either String ()
    test args@(arrlen,sza,ix) =
      let toBs nm len = [X (nm, fromInteger n) | n <- [1..len]]
          arrBs = concat [toBs ("ix"++show i) sza
                         | i <- [0..arrlen-1]
                         ]
          [arrW] = wordSplit arrBs --just zero-pads
          ixW = wordK ix
      in case runSymM (mgetBang arrlen sza arrW ixW) nullRs of
           Left err -> Left $ "Sym error: " ++ show args ++ " " ++ show err
           Right (elemW,_) ->
             let elemBs = unWordSplit [elemW]
                 expected = toBs ("ix"++show ix) sza
             in if elemBs == expected
                then return ()
                else error $ unlines [show arrlen,
                                      show sza,
                                      show arrW,
                                      show ixW,
                                      show elemW]
                  --Left $ "Mismatch: " ++ show args ++ " " ++
                    -- show (elemBs,expected)

test_msetBang_correct :: Either String ()
test_msetBang_correct =
  mapM_ test [(arrlen,sza,ix)
             | sza <- [1..32],
               arrlen <- [1..32 `div` sza],
               ix <- [0..arrlen-1]
             ]
  where
    test :: (Integer, Integer, Integer) -> Either String ()
    test args@(arrlen,sza,ix) =
      let toBs nm len = [X (nm, fromInteger n) | n <- [1..len]]
          arrBs = concat [toBs ("ix"++show i) sza
                         | i <- [0..arrlen-1]
                         ]
          [arrW] = wordSplit arrBs --just zero-pads
          ixW = wordK ix
          elemBs = toBs "elem" sza
          [elemW] = wordSplit elemBs
      in case runSymM (msetBang arrlen sza arrW ixW elemW) nullRs of
           Left err -> Left $ "Sym error: " ++ show args ++ " " ++ show err
           Right (arrW',_) ->
             let arrW'Bs = unWordSplit [arrW']
                 expected = concat [if i == ix
                                     then elemBs
                                     else toBs ("ix"++show i) sza
                                   | i <- [0..arrlen-1]
                                   ]
             in if arrW'Bs == expected
                then return ()
                else error $ unlines [show arrlen,
                                      show sza,
                                      show arrW,
                                      show ixW,
                                      show arrW']
                  --Left $ "Mismatch: " ++ show args ++ " " ++
                    -- show (elemBs,expected)

--Constructs an array by concatenating the given elements; can be implemented
--using mconstruct.
marray :: (Construct m, Op m ~ String) =>
  Integer ->   --the byte length of each element
  [[Var m]] -> --the elements
  m [Var m]    --the resulting array
marray sza es = do
  let arrlen = fromIntegral $ length es
      fields = [(fromInteger $ (arrlen-i)*sza,
                 fromInteger sza,
                 e)
               | (i,e) <- zip [1..] es
               ]
  mconstruct (fromInteger $ arrlen*sza) fields

--Given a pointer to an n-byte value in a byte-addressed region, pushes it
--to the stack.
mderefBytePtr :: (Construct m, Op m ~ String) =>
  String -> --the op: mload or calldataload
  Integer -> --byte length of referent
  Var m -> --the ptr
  m [Var m] --the result
mderefBytePtr load sz ptr = do
  --Size of the leading partial word, if any:
  let m = sz `mod` 32
      --Number of subsequent whole words
      wsz = sz `div` 32
  partial <- if m == 0
             then return []
             else (:[]) <$> opE2 "shr" (constant $ (32-m)*8) (op load [ptr])
  whole <- forM [m,m+32..m+(wsz-1)*32]
    (\k -> opE1 load $ addK k ptr)
  return $ partial ++ whole

prop_derefMem :: NonNegative Integer -> NonNegative Integer -> Bool
prop_derefMem (NonNegative sz) (NonNegative ptr) =
  let expected = map OriginalMemByte [ptr..ptr+sz-1]
  in case runSymM (mderefBytePtr "mload" sz (wordK ptr)) nullRs of
       Right (ws,_) -> let bs = unWordSplit ws
                       in if bs == expected
                          then True
                          else error $ "Mismatch: " ++ show (bs,expected)
       Left err -> error $ "SymM error: " ++ show err

--Oh no, need to mstore to scratch and mcopy as well.
--Need to ensure ptr and scratch don't overlap when testing.
--Pass scratch as a var; when writing in Fused, explore scratch and call this
--iff sz % 32 /= 0. If sz is 1, use mstore8 instead.
--No need to pass a store parameter, since memory is the only byte-addressed
--mutable region.
mwritePtrMemPartial :: (Construct m, Op m ~ String) =>
  Integer -> --sz <- [2..31]
  Var m ->   --scratch pointer
  Var m ->   --pointer
  Var m ->   --sz-byte value to write
  m ()
mwritePtrMemPartial sz scratch ptr v = do
  op0 "mstore" [scratch,v]
  --mcopy from the first byte of the value:
  --scratch' should optimize to a constant
  scratch' <- addK (32-sz) scratch
  szv <- constant sz
  op0 "mcopy" [ptr,scratch',szv]

--We don't bound the pointers, but that's fine; indeed, &(p->field) may exceed
--16b.
prop_mwritePtrMemPartial_correct ::
  NonNegative Integer -> --sz
  NonNegative Integer -> --ptr; we arbitrarily choose scratch to be ptr+32
  Bool
prop_mwritePtrMemPartial_correct (NonNegative n) (NonNegative ptr) =
  let sz = 2 + n `mod` 30 --a lot of wasted entropy there...
      bs = [X ("x", fromInteger n) | n <- [1..sz]]
      w = SymWord $ replicate (32 - fromInteger sz) (K 0) ++ bs
      scratch = ptr + 2 ^ 16 --that should be far enough away...
  in case flip runSymM nullRs (do
    mwritePtrMemPartial sz (wordK scratch) (wordK ptr) w
    written <- mapM loadMemByte [ptr..ptr+sz-1]
    written2scratch <- op "mload" [wordK scratch]
    return (written,written2scratch))
     of
       Right ((bs',w'),rs)
         | bs' /= bs ->
           error $ "Mismatch in written: " ++ show rs--(bs',bs)
         | w' /= w ->
           error $ "Scratch word mismatch: " ++ show (w',w)
         --Check only *ptr and *scratch were modified
         | let ->
           let written = M.keysSet $ symMemory rs
               toWrite = S.fromList $ [ptr..ptr+sz-1]++[scratch..scratch+31]
               diff = S.difference written toWrite
           in if not $ S.null diff
              then error $ "Wrong bytes written: " ++ show (diff, symMemory rs)
              else True
       Left err -> error $ "SymM error: " ++ show err

--Storage pointer write algo:
--To maintain the fiction of byte-addressed pointers, we must pay an
--additional runtime cost.
--startOff = ptr >> 5 --byte index => word slot
--modulus = ptr & 31  --other bytes to the left of the value
--If sz = 0, noop.
--If sz = 1, the value can only overlap with one slot:
-- s = load startOff, s' = (s[modulus] = v), store startOff s'
--Otherwise, the value can overlap with ceil(sz/32) + 0 | 1 words, depending
--on the modulus. An ifte at runtime is required.
--Left-shift the value by 32-modulus, sload and combine with the partially
--written words (using shr,shl to mask them), then store back to the
--affected indices.
--The ifte can be avoided for constant pointers using DCE.

--The written value overlaps with n+1 slots (and must be left-shifted into
--n+1 slots) if ptr%32 > constant (32-sz)%32
--If ptr%32 == (32-sz)%32, the value needs to be left-shifted 0 bytes.
--The lower ptr%32, the higher the left-shift.
--left-shift = (32-sz%32-ptr)%32
--(k-ptr)&31 is 15 gas... no savings from addmod, I'd need to negate the ptr
--and add, and are cheaper. Not surprising, addmod is for arbitrary moduli.

--Cases when combining old and new bytes:
--[{old,new}]whole*[{new,old}] |
--{old,new,old} |
--{old,new} |
--{new,old}
--Case 2 can only occur if the value is <=30 bytes and the value remains in
--one word.
--If the value is a single byte, there's no need to check whether it spills
--over into 2 words.

--For sz%32 == 0, the condition for n+1 slots becomes ptr%32 > 0; instead of
--branching on x > 0, one can branch on x.
--However, that's best applied in the opt stage; the more opts I have the
--simpler codegen I can write and still get performant code.
--Symbolic opts to use:
-- Replace div and mul (2^n) with shr, shl.
-- Replace mod (2^n) with and (2^n-1)
-- x%n is < n, <= x
-- x&n is <= x, n
-- x>0 is truthy iff x is, so if you branch on x>0 replace with x.
-- x>=0 is 1
-- x > ~0 is 0
--FW: propagate constraints from C type info to words.
--A value : T has zero bytes in its padding (<= 2^(8*sizeof T)-1).

--Evaluate a var expr and push it to scope
local :: Construct m => m (Var m) -> m (Var m)
local e = do
  scope <- getScope
  v <- e
  putScope $ v:scope
  return v

--Note I pass the actual load operation rather than just a name. That means
--that this can be reused for any API implementing a mutable word=>word map,
--e.g. storage arrays, hashmaps...
mwritePtrSto :: (Construct m, Op m ~ String) =>
  Integer -> --sizeof value to write
  (Var m -> m (Var m)) -> --load operation (used to load partially written ws)
  (Var m -> Var m -> m ()) -> --store operation (sstore or tstore)
  Var m ->     --the ptr
  [Var m] ->   --the value to write
  m ()
mwritePtrSto sz load store ptr vs
  | sz == 0 = return ()
  | let = do
          scope <- getScope
          m <- local $ opE2 "and" (constant 31) (return ptr)
          --TODO enhance SymM so it can handle non-byte shifting of constants.
          d <- local $ opE2 "shr" (constant 5) (return ptr)
          case () of
            --The value is small enough it fits in one word.
            --That means the mask may be of form 00..ff..00
            --The 0xff... part of the mask should optimize to a push for
            --small sz.
            --For sz == 1, the check whether the value should be split over
            --2 words should always return false; it should be DCE'd away.
            --Splitting cases into helper functions for readability:
            _ | sz <= 31 ->
                mwritePtrStoSzLT32 sz load store ptr vs scope m d
              --The value is a whole number of words
              | sz `mod` 32 == 0 ->
                mwritePtrStoSzMod32Eq0 sz load store ptr vs scope m d
              | let ->
                mwritePtrStoSzGt32Mod32Neq0 sz load store ptr vs scope m d
          --Reset the scope
          putScope scope

mwritePtrStoSzLT32 :: (Construct m, Op m ~ String) =>
  Integer -> --sizeof value to write
  (Var m -> m (Var m)) -> --load operation (used to load partially written ws)
  (Var m -> Var m -> m ()) -> --store operation (sstore or tstore)
  Var m ->     --the ptr
  [Var m] ->   --the value to write
  [Var m] -> --scope
  Var m -> --sz % 32
  Var m -> --sz / 32
  m [Var m] --empty return list; TODO replace with ()
mwritePtrStoSzLT32 sz load store ptr vs scope m d = do
  --unsafePrint "sz <= 31"
  let [w] = vs
  --For sz = 1:
  --m = 31 => left-shift = 0, it increases with lower m
  --left-shift in bytes: 31-m
  --Instead of *8, I can use shl 3, saving 2 gas
  --General leftshift:
  --8*(32-sz-m)%32
  lsh <- local $ opE2 "shl" (constant 3) $
         opE2 "and" (constant 31) $
         opE2 "sub" (constant $ 32-sz) $
         return m
  --If m > 32-sz, the value must be split into two words
  --Note if sz == 1, that's impossible since m = _ % 32.
  ifte 0 (opE2 "gt" (return m) $ constant $ 32 - sz)
    --w must be split across two words:
    (do rsh <- opE2 "sub" (constant 256) (return lsh)
        --Low and high here refers to LSB and MSB respectively;
        --MSB is at the lowest address.
        lo <- op "shl" [lsh,w]
        hi <- op "shr" [rsh,w]
        --The pre-shift mask should ofc have the same
        --sz as the value...
        ff <- (constant $ 8*sz) >>= bitmask
        maskLo <- opE1 "not" $ op "shl" [lsh,ff]
        maskHi <- opE1 "not" $ op "shr" [rsh,ff]
        storeWithMask load store maskHi d hi
        d_plus_1 <- addK 1 d
        storeWithMask load store maskLo d_plus_1 lo
        return []
    )
    --w is still one word:
    (do w' <- op "shl" [lsh,w]
        wbits <- (constant $ 8*sz) >>= bitmask
        mask <- opE1 "not" $ op "shl" [lsh,wbits]
        storeWithMask load store mask d w'
        return []
    )
mwritePtrStoSzMod32Eq0 :: (Construct m, Op m ~ String) =>
  Integer -> --sizeof value to write
  (Var m -> m (Var m)) -> --load operation (used to load partially written ws)
  (Var m -> Var m -> m ()) -> --store operation (sstore or tstore)
  Var m ->     --the ptr
  [Var m] ->   --the value to write
  [Var m] -> --scope
  Var m -> --sz % 32
  Var m -> --sz / 32
  m [Var m] --empty return list; TODO replace with ()
mwritePtrStoSzMod32Eq0 sz load store ptr vs scope m d =
  ifte 0 (return m)
  --The value must be left-shifted; the first and last words
  --must be partially written.
  --Since the minimum number of words resulting is two, there's
  --guaranteed to be a distinct first and last word.
  (do lsh <- opE2 "shl" (constant 3) $
             opE2 "sub" (constant 32) $
             return m
      vs' <- mdynLeftShiftNPlus1 vs lsh
      let fi = head vs'
          mid = init $ tail vs'
          la = last vs'
      --Store first word:
      --A mask with 256-lsh 1-bits to the left:
      --Is sharing the mask computation worth it?
      mask <- opE2 "shl" (return lsh) $
              opE1 "not" $ constant 0
      storeWithMask load store mask d fi
      --Store the middle words:
      --If there are none, the add will be optimized away
      do d_plus_1 <- addK 1 d
         writeSlots store d_plus_1 mid
         --Store the last word:
      slot <- addK (fromIntegral $ length $ fi:mid) d
      flippedMask <- op "not" [mask]
      storeWithMask load store flippedMask slot la
      return []
  )
  --the value can be written as-is:
  (writeSlots store d vs >> return [])
mwritePtrStoSzGt32Mod32Neq0 :: (Construct m, Op m ~ String) =>
  Integer -> --sizeof value to write
  (Var m -> m (Var m)) -> --load operation (used to load partially written ws)
  (Var m -> Var m -> m ()) -> --store operation (sstore or tstore)
  Var m ->     --the ptr
  [Var m] ->   --the value to write
  [Var m] -> --scope
  Var m -> --sz % 32
  Var m -> --sz / 32
  m [Var m] --empty return list; TODO replace with ()
mwritePtrStoSzGt32Mod32Neq0 sz load store ptr vs scope m d =
  do
    --unsafePrint "sz > 32, sz % 32 != 0"
    --Mostly copied from sz<=31 case; TODO merge...
    --For sz = 1:
    --m = 31 => left-shift = 0, it increases with lower m
    --left-shift in bytes: 31-m
    --Instead of *8, I can use shl 3, saving 2 gas
    --General leftshift:
    --8*(32-sz-m)%32
    lsh <- local $ opE2 "shl" (constant 3) $
           opE2 "and" (constant 31) $
           opE2 "sub" (constant $ 32-(sz`mod`32)) $
           return m
    --If m > 32-sz, the value must be split into n+1 words
    --Note if sz == 1, that's impossible since m = _ % 32.
    ifte 0 (opE2 "gt" (return m) $ constant $ 32 - (sz`mod`32))
      --the value must be split into n+1 words
      (do vs' <- mdynLeftShiftNPlus1 vs lsh
          --unsafePrint $ "T: " ++ show vs'
          let fi = head vs'
              mid = init $ tail vs'
              la = last vs'
          --Writing the first word:
          --the number of value bits in the first word:
          --Because it's overflowed, we must also %32B
          fibits <-
            opE2 "and" (constant 255) $
            opE2 "add" (constant $ 8*(sz`mod`32))
            (return lsh)
          --unsafePrint $ "fibits: " ++ show fibits
          fimask <- opE2 "shl" (return fibits) $
                    opE1 "not" (constant 0)
          --unsafePrint $ "fimask: " ++ show fimask
          storeWithMask load store fimask d fi
          --Store the middle words:
          do d_plus_1 <- addK 1 d
             writeSlots store d_plus_1 mid
          --Store the last word:
          --The lower shl bits should not be overwritten
          mask <- bitmask lsh
          slot <- addK (fromIntegral $ length $ fi:mid) d
          storeWithMask load store mask slot la
          return []
      )
      --The value remains n>=2 words
      (do vs' <- mdynLeftShiftN vs lsh
          --unsafePrint $ "F: " ++ show vs'
          let fi = head vs'
              mid = init $ tail vs'
              la = last vs'
          --Writing first word:
          --No need to %32 since there was no overflow
          fibits <- opE2 "add" (constant $ 8*(sz`mod`32))
                    (return lsh)
          fimask <- opE2 "shl" (return fibits) $
                    opE1 "not" (constant 0)
          storeWithMask load store fimask d fi
          --Store the middle words:
          do d_plus_1 <- addK 1 d
             writeSlots store d_plus_1 mid
          --Store the last word:
          mask <- bitmask lsh
          slot <- addK (fromIntegral $ length $ fi:mid) d
          storeWithMask load store mask slot la
          return []
      )
  
--Write words to slot, slot+1..
writeSlots :: (Construct m, Op m ~ String) =>
  (Var m -> Var m -> m ()) ->
  Var m -> [Var m] -> m ()
writeSlots store slot vs =
  zipWithM_ (\off v -> do
                slot' <- addK off slot
                store slot' v) [0..] vs  
--Load old value, mask it, or it with value to write, write back
storeWithMask :: (Construct m, Op m ~ String) =>
  (Var m -> m (Var m)) ->     --load operation
  (Var m -> Var m -> m ()) -> --store operation
  Var m -> --mask
  Var m -> --slot
  Var m -> --value
  m ()
storeWithMask load store mask slot value = do
  old <- load slot
  new <- opE2 "or" (op "and" [mask,old]) $ return value
  store slot new

--Given a number of bits n, create a mask with min(n,256) 1-bits, right-aligned.
bitmask :: (Construct m, Op m ~ String) => Var m -> m (Var m)
bitmask n = opE2 "sub" (opE2 "shl" (return n) (constant 1)) (constant 1)
{-
--storeWithMask, with mask = shl lower bits (and shl is dynamic)
storeInUpperBits load store shl slot value = do
  mask <- opE2 "sub" (opE2 "shl" (return shl) (constant 1)) $ constant 1
  storeWithMask load store mask slot value
storeInLowerBits load store shl
-}

--Shift a value stored across multiple words left by sh <- [0..31] bytes,
--with the constraint that the result is still equally many words.
--Algo: the words = init++[last].
--Each word should be left-shifted by sh, then or'd with the spillover from the
--word to the right of it (right-shifted by 32B-sh).
--The last word has no word to the right of it, so it's just left-shifted.
mdynLeftShiftN :: (Construct m, Op m ~ String) =>
  [Var m] -> --the value to left-shift
  Var m -> --the left-shift, a dynamic value
  m [Var m] --the result
mdynLeftShiftN ws sh =
  case ws of
    [] -> return []
    _ -> do
      shld <- mapM (\w -> op "shl" [sh,w]) ws
      rsh <- opE2 "sub" (constant 256) (return sh)
      spillover <- mapM (\w -> op "shr" [rsh,w]) $ tail ws
      go shld spillover
  where go shld [] = return shld --one elem
        go (w:ws) (r:rs) = do
          u <- op "or" [w,r]
          us <- go ws rs
          return $ u:us

--The left-padding is (32-sz%32)%32 bytes... left-shift must be <= that.
prop_mdynLeftShiftN_correct ::
  Positive Integer -> --sz
  NonNegative Int -> --lsh in bytes before modulus
  Bool
prop_mdynLeftShiftN_correct (Positive sz) (NonNegative lsh_pre_mod) =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      vBs = toBs "v" $ fromInteger sz
      vWs = wordSplit vBs
      leftPadding = (32 - sz `mod` 32) `mod` 32
      lsh = 8 * (fromIntegral lsh_pre_mod `mod` (leftPadding + 1))
  in case runSymM (mdynLeftShiftN vWs (wordK lsh)) nullRs of
       Right (actualWs,_) ->
         let actualBs = actualWs >>= \(SymWord bs) -> bs
             expectedBs = replicate (fromInteger $ leftPadding - lsh`div`8)
                          (K 0) ++
                          vBs ++
                          replicate (fromInteger (lsh`div`8)) (K 0)
         in if actualBs /= expectedBs
            then error $ "Mismatch: " ++ show (actualBs,expectedBs)
            else True
       Left err -> error $ "SymM error: " ++ show err
--Constraint: the result is n+1 words, where n is the original word length.
--Precondition: ws is nonempty.
mdynLeftShiftNPlus1 :: (Construct m, Op m ~ String) =>
  [Var m] ->
  Var m   ->
  m [Var m]
mdynLeftShiftNPlus1 ws sh = do
  --This duplicate expression should be optimized away...
  rsh <- opE2 "sub" (constant 256) (return sh)
  tl <- mdynLeftShiftN ws sh
  hd <- op "shr" [rsh, head ws]
  return $ hd:tl
--Left-padding: (32-sz%32)%32
--In this case lsh is between that and 31
prop_mdynLeftShiftNPlus1_correct (Positive sz) (NonNegative lsh_pre_mod) =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      vBs = toBs "v" $ fromInteger sz
      vWs = wordSplit vBs
      leftPadding = (32 - sz `mod` 32) `mod` 32
      lsh = 8 * (leftPadding +
                 fromIntegral lsh_pre_mod `mod` (32-leftPadding))
  in case runSymM (mdynLeftShiftNPlus1 vWs (wordK lsh)) nullRs of
       Right (actualWs,_) ->
         let actualBs = actualWs >>= \(SymWord bs) -> bs
             expectedBs = replicate (fromInteger $ 32 + leftPadding - lsh`div`8)
                          (K 0) ++
                          vBs ++
                          replicate (fromInteger (lsh`div`8)) (K 0)
         in if actualBs /= expectedBs
            then error $ "Mismatch: " ++ show (actualBs,expectedBs)
            else True
       Left err -> error $ "SymM error: " ++ show err

--Storage and tstorage have equivalent behavior (for the duration of
--mwritePtrSto), so I only need to test for storage.
--Correctness property: when writing a sz-byte value bs to byte offset
-- >= 0 (but not >= 2^256, which QuickCheck thankfully doesn't gen),
--the resulting storage has bs at the given offset and everything else
--untouched.
prop_mwritePtrSto_correct ::
  Positive Integer -> --sizeof value to write
  NonNegative Integer -> --ptr
  Bool
prop_mwritePtrSto_correct (Positive sz) (NonNegative ptr)  =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      vBs = toBs "v" $ fromInteger sz
      vWs = wordSplit vBs
      load w = op "sload" [w]
      store off w = op0 "sstore" [off,w]
      d = ptr `div` 32
      m = ptr `mod` 32
      --The byte offsets of the value should be ptr..ptr+sz-1
      lastOff = (ptr+sz-1) `div` 32
      touched = [d..lastOff]
  in case flip runSymM nullRs $ do
    mwritePtrSto sz load store (wordK ptr) vWs
    mapM (\slot -> constant slot >>= load) touched
     of
       Right (shiftedVs,rs) ->
         --Concatenate all symbytes:
         let bs = shiftedVs >>= \(SymWord bs) -> bs
             --It should consist of m original bytes, sz value bytes,
             --and the rest original.
             [mn,szn] = map fromInteger [m,sz]
             untouchedLeft = take mn bs
             rest = drop mn bs
             writtenValue = take szn rest
             untouchedRight = drop szn rest
             --Expected values:
             originalBytes = map OriginalStoByte [fromInteger (d*32)..]
             expectedLeft = take mn originalBytes
             expectedWritten = vBs
             expectedRight = drop (mn+szn) $ take (32*length shiftedVs)
                             originalBytes
             actual = (untouchedLeft,writtenValue,untouchedRight)
             expected = (expectedLeft,expectedWritten,expectedRight)
         in case () of
              _ | actual /= expected ->
                  error $ unlines ["Mismatch:",
                                   "L: " ++ show (untouchedLeft,
                                                  expectedLeft),
                                   "W: " ++ show (writtenValue,
                                                  expectedWritten),
                                   "RA: " ++ show untouchedRight,
                                   "RE: " ++ show expectedRight
                                  ]
                | let sto = symStorage rs
                      ks = M.keysSet sto ->
                  if ks /= S.fromList touched
                  then error $ "Wrong slots touched: " ++ show (ks,touched)
                  else True
       Left err -> error $ "Sym eval error: " ++ show err

--Deref a sz-byte value from a word=>word map; used to implement
--deref for Storage and TStorage.
--I need to do the inverse of writing: load the same words, but instead
--right-shift.
--The same cases are relevant: 0 bytes, 1 byte, larger.
--Rely on symbolic opt to simply the cond check in sz = 32n.
--Spillover condition: ceil(sz+m div 32) > ceil(sz div 32)
--That's equivalent to m > (32-sz%32)%32
--Might as well quickcheck that!
prop_cond_simpl_correct ::
  NonNegative Integer ->
  NonNegative Integer ->
  Bool
prop_cond_simpl_correct (NonNegative sz) (NonNegative m) =
  (wcnt (sz + m) > wcnt sz) ==
  (m > (32-sz`mod`32)`mod`32)
  where wcnt n =
          (if n `mod` 32 > 0
           then succ
           else id) (n `div` 32)
mderefWordPtr :: (Construct m, Op m ~ String) =>
 String -> Integer -> Var m -> m [Var m]
mderefWordPtr load sz ptr
  | sz == 0 = return []
  | let = do
          scope <- getScope
          slot <- local $ opE2 "shr" (constant 5) (return ptr)
          m <- local $ opE2 "and" (constant 31) (return ptr)
          --The word count of the deref'd type:
          let wcnt = (if sz `mod` 32 > 0
                      then succ
                       else id) (sz `div` 32)
          retws <- case () of
            _ | sz == 1 -> (:[]) <$> opE2 "byte" (return m) (op load [slot])
              | sz `mod` 32 == 0 ->
                ifte (fromInteger wcnt) (return m)
                --Special case: no need to mask the top word
                (do ws <- forM [0..wcnt] (\i -> opE1 load (addK i slot))
                    rsh <- opE2 "shl" (constant 3) $
                           opE2 "sub" (constant 32) (return m)
                    wsr <- mapM (\w -> op "shr" [rsh,w]) $ tail ws
                    lsh <- opE2 "sub" (constant 256) (return rsh)
                    wsl <- mapM (\w -> op "shl" [lsh,w]) $ init ws
                    zipWithM (\a b -> op "or" [a,b]) wsl wsr
                )
                --The cheapest case
                (forM [0..wcnt-1]
                (\i -> opE1 load (addK i slot)))
              | let -> do
                  --The amount to right-shift by:
                  --TODO opt: % k distributes over summands; & (2^n-1) = % 2^n
                  --That lets you replace 32 with 0 here.
                  --Also: if the constant is 31, 0 <= 31-m <= 31
                  --so % 32 is a noop
                  rsh <- local $ opE2 "shl" (constant 3) $
                         opE2 "and" (constant 31) $
                         opE2 "sub" (constant (32 - sz `mod` 32)) (return m)
                  --Masking is handled here rather than in ...RightShift...
                  --the gas cost is the same but the code size will be larger.
                  --TODO opt (w >> k) & mask to ((w << k1) >> k2)
                  ifte (fromInteger wcnt)
                    (opE2 "gt" (return m)
                      (constant $ (32 - sz`mod`32) `mod` 32))
                  --Overflow into wcnt+1 words:
                    (do ws <- forM [0..wcnt]
                          (\i -> opE1 load (addK i slot))
                        ws' <- mdynRightShiftNPlus1 ws rsh
                        maskTopWord ws'
                    )
                    --No overflow:
                    (do ws <- forM [0..wcnt-1]
                          (\i -> opE1 load (addK i slot))
                        ws' <- mdynRightShiftN ws rsh
                        maskTopWord ws'
                    )
          putScope $ retws ++ scope
          return retws
            where maskTopWord :: (Construct m, Op m ~ String) =>
                                 [Var m] -> m [Var m]
                  maskTopWord (w:ws) = do
                    w' <- opE2 "and" (constant $ 256 ^ (sz `mod` 32) - 1)
                          (return w)
                    return $ w':ws


--rsh = 8n, n <- 1..31
--Precondition: length ws >= 2.
--The resulting list is one word shorter: the argument is len n+1, where
--n is the word count of the deref'd value.
mdynRightShiftNPlus1 :: (Construct m, Op m ~ String) =>
  [Var m] -> Var m -> m [Var m]
mdynRightShiftNPlus1 ws rsh = do
  wsr <- mapM (\w -> op "shr" [rsh,w]) $ tail ws
  lsh <- opE2 "sub" (constant 256) (return rsh)
  wsl <- mapM (\w -> op "shl" [lsh,w]) $ init ws
  zipWithM (\a b -> op "or" [a,b]) wsl wsr

--Precond: length ws >= 1
--The resulting list is the same length.
mdynRightShiftN :: (Construct m, Op m ~ String) =>
  [Var m] -> Var m -> m [Var m]
mdynRightShiftN ws rsh = do
  ws' <- mdynRightShiftNPlus1 ws rsh
  w' <- op "shr" [rsh, head ws]
  return $ w':ws'

--Round-trip property: if you first write and then deref a value to a
--ptr, you get the same value back.
--It implies the standalone correctness property given the correctness
--of mwritePtrSto (which is already tested).
prop_stoPtr_round_trip :: NonNegative Integer -> NonNegative Integer -> Bool
prop_stoPtr_round_trip (NonNegative ptr) (NonNegative sz) =
  let toBs nm len = [X (nm,n) | n <- [1..len]]
      vBs = toBs "v" $ fromInteger sz
      vWs = wordSplit vBs
      load a = op "sload" [a]
      store a b = op0 "sstore" [a,b]
  in case runSymM (do mwritePtrSto sz load store (wordK ptr) vWs
                      mderefWordPtr "sload" sz (wordK ptr)
                  ) nullRs of
       Right (ws,_) ->
         let actualBs = unWordSplit ws
         in if actualBs == vBs
            then True
            else error $ "Mismatch: " ++ show (actualBs,vBs)
       Left err -> error $ "SymM error: " ++ show err

--Apparently even something as simple as coerce is worth implementing in
--Construct - the version defined in Fused was buggy!
--unsafeCoerce: if arg has more words, truncate; otherwise leftpad with
--zeroes.
--Should error if the number of words given is wrong.
munsafeCoerce :: (Construct m, Op m ~ String) =>
 Integer -> Integer -> [Var m] -> m [Var m]
munsafeCoerce sza szb ws = do
  let [wa,wb] = map wordLen [sza,szb]
  if wa /= fromIntegral (length ws)
    then error "Incorrect number of words given to munsafeCoerce!"
    else return ()
  case () of
    _ | wa == wb -> return ws
      | wa > wb -> return $ drop (fromInteger $ wa - wb) ws
      | wa < wb -> do
          z <- constant 0
          return $ replicate (fromInteger $ wb - wa) z ++ ws

--Byte length => word length
wordLen :: Integer -> Integer
wordLen bs = (bs `roundedUpMod` 32) `div` 32
  
--coerce arg = unsafeCoerce arg; if the top result word is partial and
--sza > szb, mask it.
mcoerce :: (Construct m, Op m ~ String) =>
           Integer -> Integer -> [Var m] -> m [Var m]
mcoerce sza szb ws = do
  ws' <- munsafeCoerce sza szb ws
  let m = szb `mod` 32
  if m > 0 && sza > szb
    then do
    let r:rs = ws'
    --A word can always be masked code-inefficiently for 6 gas using and k.
    --Alt: shl, shr. For now I'll use the code-inefficient maskBytes
    r' <- maskBytes m r
    return $ r':rs
    else return ws'

prop_munsafeCoerce :: NonNegative Integer -> NonNegative Integer -> Bool
prop_munsafeCoerce sza (NonNegative szb) =
  prop_coercion munsafeCoerce sza (NonNegative $ szb `roundedUpMod` 32)
prop_mcoerce :: NonNegative Integer -> NonNegative Integer -> Bool
prop_mcoerce = prop_coercion mcoerce

--At runtime coerce is more complex than unsafeCoerce, but it's simpler to
--test! munsafeCoerce sza szb = mcoerce sza (szb `roundedUpMod` 32)
prop_coercion ::
  (Integer -> Integer -> [SymWord] -> SymM [SymWord]) ->
  NonNegative Integer -> NonNegative Integer -> Bool
prop_coercion coercion (NonNegative sza) (NonNegative szb) =
  let argBs = [X ("a", fromInteger n) | n <- [1..sza]]
      argWs = wordSplit argBs
  in case runSymM (coercion sza szb argWs) nullRs of
       Right (retWs,_) ->
         let retBs = unWordSplit retWs
         in if sza <= szb
            then match retBs argBs
            else match retBs $ reverse
                 (take (fromInteger szb) $ reverse argBs)
       Left err -> error $ "Error in prop_coercion: " ++ show err
  where match a b =
          if a == b
          then True
          else error $ "Mismatch " ++ show (a,b)
