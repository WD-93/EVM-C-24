{-# LANGUAGE LambdaCase, TypeFamilies,
GeneralizedNewtypeDeriving, TypeOperators #-} --for monadic mocking
module Construct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State
--For monadic implementation:
import Control.Monad.Writer
import Control.Monad (zipWithM, forM)
import Data.Bits ((.&.),(.|.),complement) --for symbolic eval
import AST.DTs (roundedUpMod)
--Testing:
import Test.QuickCheck hiding ((.&.),(.|.),output)

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
  --Debug comments:
  comment :: String  -> m ()

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
  constant k = Emit $ do
    n <- get
    put (n+1)
    let v = Left n
    tell [Push v k]
    return v
  comment str = Emit $ tell [Comment str]

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
             | X (String,Int) --(id,n)
  deriving (Eq,Show)
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
newtype SymM a = SymM {runSymM :: Either SymError a}
  deriving (Functor, Applicative, Monad)
data SymError = NotAByteConst SymWord
              | NotMul8 SymOp SymWord
              | BadArity SymOp [SymWord]
              | Can'tSimpBB SymOp SymByte SymByte
              | Can'tSimpNB SymOp Int SymByte
              | Can'tNOT SymByte
              | Can'tHandleSym String SymByte
  deriving (Eq,Show)
instance Construct SymM where
  type Var SymM = SymWord
  type Op SymM = SymOp
  constant n = SymM $ return $ wordK n
  op o [a,b] = SymM $
    case o of
      "byte" ->
        --If ix > 31, return 0
        case parseByte a of
          Right ix | ix < 32 ->
                     let SymWord bs = b
                     in return $ SymWord $ replicate 31 (K 0) ++ [bs !! ix]
      --I'm starting to stretch the limits of what is convenient with this
      --simple monad...
      --For now support only for concrete values.
      "add" -> concreteWordOp2 "add" (+) a b
      "mul" -> concreteWordOp2 "mul" (*) a b
      _ | o `elem` ["shr","shl"] -> do
            shBits <- parseByte a
            if (shBits `mod` 8) /= 0
              then Left $ NotMul8 o a
              else return ()
            let shBytes = shBits `div` 8
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
  op "not" [SymWord bs] = SymM $ SymWord <$> mapM symNot bs
  op o ws = SymM $ Left $ BadArity o ws
  comment _ = return ()

--Inefficient... if I want fast symbolic eval in future need to make byte-level
--symbolic repr optional.
concreteWordOp2 :: String ->
                   (Integer -> Integer -> Integer) ->
                   SymWord -> SymWord -> Either SymError SymWord
concreteWordOp2 op f (SymWord as) (SymWord bs) = do
  a <- parse as
  b <- parse bs
  return $ wordK $ f a b `mod` (2 ^ 256)
  where parse symBs = do
          bs <- forM symBs (\case K n -> return n
                                  sym -> Left $ Can'tHandleSym op sym)
          return $ go 1 $ reverse bs
        go mul = \case
          [] -> 0
          b:bs -> (mul * fromIntegral b) + go (mul*256) bs
          
--I just need to test bitwise not on constants for now, no need to extend
--the symbolic byte repr.
symNot :: SymByte -> Either SymError SymByte
symNot = \case
  K n -> return $ K $ complement n .&. 0xff
  b -> Left $ Can'tNOT b
  
apply :: SymOp -> SymByte -> SymByte -> Either SymError SymByte
apply o (K a) (K b) =
  return $ K $ appK o a b
apply "and" (K n) x = simpAnd n x
apply "and" x (K n) = simpAnd n x
apply "or" (K n) x = simpOr n x
apply "or" x (K n) = simpOr n x
apply o a b
  | a == b = return a
  | let = Left $ Can'tSimpBB o a b
simpAnd n x =
  case n of
    0 -> return $ K 0
    255 -> return x
    _ -> Left $ Can'tSimpNB "and" n x
simpOr n x =
  case n of
    0 -> return x
    255 -> return $ K 255
    _ -> Left $ Can'tSimpNB "or" n x
appK o a b =
  case o of
    "and" -> a .&. b
    "or" -> a .|. b
    _ -> error $ "Unexpected op in appK: " ++ o
  
--Errors if not byte constant.
parseByte :: SymWord -> Either SymError Int
parseByte w@(SymWord (b:bs)) = go b bs
  where go (K n) [] = return n
        go (K 0) (b:bs) = go b bs
        go _ _ = Left $ NotAByteConst w

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
                   structWs) of
       Right fld ->
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
  in case runSymM $ mconstruct (sum ns) wfs of
       Right ws ->
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
                   oldStructWs newFieldWs) of
       Right struct' ->
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
      in case runSymM (mgetBang arrlen sza arrW ixW) of
           Left err -> Left $ "Sym error: " ++ show args ++ " " ++ show err
           Right elemW ->
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
