{-# LANGUAGE LambdaCase, TypeFamilies,
GeneralizedNewtypeDeriving#-} --for monadic mocking
module Construct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
--For monadic mocking:
import Control.Monad.Writer
import Control.Monad (zipWithM)
import Data.Bits ((.&.),(.|.)) --for symbolic eval


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
  op :: Op m ->
        [Var m] -> --args
        m (Var m)
  --Need to add constant to support shr. That strongly restricts vars to
  --representing integer-like things.
  --Alt: make shr, shl k ops.
  constant :: Integer -> m (Var m)
  --Perhaps enhance with debug comments

--Separating interpretations lets you simplify the respective monads.
--Interpretation 1: emit instructions, allocate new vars.
--Free monads could be used here.
--Problem: I pass in vars from the outside. How to represent them?
type V v = Either Int v
newtype Emit v a = Emit {unEmit :: StateT Int (Writer [(V v,String,[V v])]) a}
  deriving (Functor, Applicative, Monad)
runEmit :: Emit v a -> Int -> (a,[(V v,String,[V v])],Int)
runEmit (Emit sra) n =
  let ((a,s),w) = runWriter $ runStateT sra n
  in (a,w,s)
instance Construct (Emit v) where
  type Var (Emit v) = V v
  type Op (Emit v) = String
  op str vs = Emit $ do
    n <- get
    put (n+1)
    let v = Left n
    tell [(v, str, vs)]
    return v
  constant n = error "Not defined"

emitM1 :: Emit String (V String)
emitM1 = do
  let [a,b,c] = map Right $ words "a b c"
  x <- op "+" [a,b]
  y <- op "+" [x,c]
  return y

--Symbolic eval interpretation; this is the one used for tests.
--It doesn't need any alloc machinery since "vars" are simply symbolic values.
newtype SymWord = SymWord [SymByte] --length = 32
  deriving (Eq,Show)
data SymByte = K Int --0..255
             | X (String,Int) --(id,n); n <- 0..31
  deriving (Eq,Show)
--The ops relevant to struct construction and access.
--I don't need push since I'm evaluating rather than generating
--instructions; the constant in the instance can handle that.
data SymOp = SHL
           | SHR
           | AND
           | OR
  deriving (Eq,Ord,Read,Show)
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
newtype SymM a = SymM (Either SymError a)
  deriving (Functor, Applicative, Monad)
data SymError = NotAByteConst SymWord
              | NotMul8 SymOp SymWord
              | BadArity SymOp [SymWord]
              | Can'tSimpBB SymOp SymByte SymByte
              | Can'tSimpNB SymOp Int SymByte
  deriving (Eq,Show)
instance Construct SymM where
  type Var SymM = SymWord
  type Op SymM = SymOp
  constant n = SymM $ return $ wordK n
  op o [a,b] = SymM $
    if o `elem` [SHR,SHL]
    then do
      shBits <- parseByte a
      if (shBits `mod` 8) /= 0
        then Left $ NotMul8 o a
        else return ()
      let shBytes = shBits `div` 8
          zeroes = replicate shBytes $ K 0
          SymWord bs = b
      return $ SymWord $
        case o of
          SHR -> take 32 $ zeroes ++ bs
          SHL -> reverse $ take 32 $ zeroes ++ reverse bs
      --While partial-byte shift is possible in the EVM, I don't use
      --it; just error if a % 8 /= 0.
      --If any byte above the lowest isn't K 0, error.
      --Otherwise shift by a/8 bytes.
      else do
      let SymWord as = a
          SymWord bs = b
      SymWord <$> zipWithM (apply o) as bs
  op o ws = SymM $ Left $ BadArity o ws
apply :: SymOp -> SymByte -> SymByte -> Either SymError SymByte
apply o (K a) (K b) =
  return $ K $ appK o a b
apply AND (K n) x = simpAnd n x
apply AND x (K n) = simpAnd n x
apply OR (K n) x = simpOr n x
apply OR x (K n) = simpOr n x
apply o a b
  | a == b = return a
  | let = Left $ Can'tSimpBB o a b
simpAnd n x =
  case n of
    0 -> return $ K 0
    255 -> return x
    _ -> Left $ Can'tSimpNB AND n x
simpOr n x =
  case n of
    0 -> return x
    255 -> return $ K 255
    _ -> Left $ Can'tSimpNB OR n x
appK o a b =
  case o of
    AND -> a .&. b
    OR -> a .|. b
  
--Errors if not byte constant.
parseByte :: SymWord -> Either SymError Int
parseByte w@(SymWord (b:bs)) = go b bs
  where go (K n) [] = return n
        go (K 0) (b:bs) = go b bs
        go _ _ = Left $ NotAByteConst w
