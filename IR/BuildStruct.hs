{-# LANGUAGE LambdaCase #-}
module IR.BuildStruct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Arrow ((***))
import Data.List (sortOn)

import DTs (Padding(..),padWith,roundedUpMod)

--It's parameterized by input type so we can both debug and use it easily
--Debug parameter: (String,Int)
--Real: Name (used for vars in IR)
data O i = V i Int --Int: select nth word
       | Shift (O i) Int --left shift, -ve is right shift
       | O i :|| O i
  deriving (Eq,Ord,Read)
instance Show i => Show (O i) where
  show (V i ix) = show i ++ "[" ++ show ix ++ "]"
  show (Shift o n)
    | n > 0 = show o ++ " << " ++ show n
    | n < 0 = show o ++ " >> " ++ show (-n)
    | otherwise = error $  "Should be normed away: " ++ show (o,n)
  --Note this show is ambiguous...
  show (o1 :|| o2) = show o1 ++ " | " ++ show o2
shift :: O i -> Int -> O i
shift o 0 = o
shift o n = Shift o n
(.<<) :: O i -> Int -> O i
o .<< n | n < 0 = error "Badarg in .<<"
        | let = Shift o n
o .>> n | n < 0 = error "Badarg in .>>"
        | let = Shift o (-n)

--Represents the list of words of nm, a C value of bitsize sz
--It's 1-indexed: a 257-bit value x becomes (257,[("x",1),("x",2)])
type Value i = (Int,[i])
value :: Int -> String -> Value (String,Int)
value sz nm =
  let wsz = (sz `roundedUpMod` 256) `div` 256
  in (sz,[(nm,i) | i <- [1..wsz]])

--Now we deduplicate the logic for struct size calculation, creation and
--access: given a list of fields, compute layout in terms of left-offset and
--bitsize per field.
--Bitsize of struct = sz of first field + its offset
--Creation: insert each word of field at offset, offset + 256, ...
--Access: ...
--The logic, including for field access, can go here; just interpret it in IR.
--Niggle: should 0-size fields trigger alignment? No.

--(struct bitsize,[(field bitsize,offset from the left)])
--Why the first Int? Because the leftmost field is padded too, so when reading
--the struct from memory you may assume that pad exists.
--Bug: zero-size fields should be ignored when considering alignment;
--instead of rounding up the next offset based on the alignment of the next
--field, round up your own offset based on your own alignment.
--Nice, that's actually simpler.
type StructLayout = (Int,[(Int,Int)])
structLayout :: [(Padding,Padding,Int)] -> StructLayout
structLayout padalszs = go padalszs
  where go = \case
          [] -> (0,[])
          (pad,al,sz):rest ->
            let (off,fs) = go rest
                myOff = off `padWith` al
                nextOff = (myOff + sz) `padWith` pad
            in (nextOff,(sz,myOff):fs)
  {-
  let als = map (\(pad,al,sz) -> al) padalszs
      --Associate each field with alignment of next, or Bit (noop) for
      --leftmost
      padalszs' = zipWith (\al (pad,_,sz) -> (pad,al,sz)) (Bit:als) padalszs
      --Offset after each field: (off + (sz paddedWith pad)) paddedWith al
  in go padalszs'
  where go [] = (0,[])
        go ((pad,al,sz):rest) =
          let (off,fs) = go rest
               --Special case: 0-sized fields ignore alignment
              al' = if sz == 0 then Bit else al
          in ((off + (sz `padWith` pad)) `padWith` al',
              (sz,off):fs)
-}
--The creation logic needn't be handed the list of words; O has a concept of
--nth word via V.
--For each field (sz,off) i, split into words and place them at off, off+256..
createStruct :: StructLayout -> [i] -> [O i]
createStruct (_,layout) is =
  let i2o = flip execState M.empty $ zipWithM handleField layout is
  in reverse $ M.elems i2o
  where handleField (sz,off) i =
          let wszs = tagWordsWithSize sz $ splitIntoWords sz i
          in zipWithM (\off (w,sz) -> placeWord off sz w) [off,off+256..] $
             reverse wszs
             
--The struct builder monad
--We eliminate the Ord constraint on i by mapping from struct word index to
--a single O, which we modify by or-ing it with field words.
--Inv: no nonexistent words of i's (the second word of a uint8, for example).
--Inv: no empty struct words.
type SB i = State (Map Int (O i))
--sz matters because it determines whether a value will spill over into the
--next word.
placeWord :: Int -> Int -> O i -> SB i ()
placeWord off sz w = do
  --The first struct word to add w to
  let startW = off `div` 256
  insertWord startW (w `shift` (off `mod` 256))
  let endW = (off + sz - 1) `div` 256
  if endW /= startW
    then insertWord endW (w `shift` ((off `mod` 256)-256))
    else return ()
insertWord :: Int -> O i -> SB i ()
insertWord i o = modify $ M.alter (Just . (\case Nothing -> o
                                                 Just o' -> o' :|| o)
                                  ) i
splitIntoWords :: Int -> i -> [O i]
splitIntoWords sz i = [V i n | n <- [1.. (sz `padWith` Word) `div` 256]]
--Given a list of words containing a value and the bitsize of that value, tag
--each word with the number of bits of the value it contains.
tagWordsWithSize :: Int -> [a] -> [(a,Int)]
tagWordsWithSize 0 [] = []
tagWordsWithSize sz (w:ws)
  | sz `mod` 256 > 0 = (w,sz`mod`256): map (\w -> (w,256)) ws
  | otherwise = map (\w -> (w,256)) (w:ws)

--For struct field access:
--struct<i1><i2>... => result offset = sum of offsets
--BuildStruct has no concept of nested structs, so here we just need to
--give the size and offset of the nth field (if there is one).
getFieldInfo :: StructLayout -> Int -> Maybe (Int,Int)
getFieldInfo (sz,szoffs) n = go szoffs n
  where
    go (szoff:_) 0 = Just szoff
    go (_:rest) n | n > 0 = go rest (n-1)
    go _ _ = Nothing


--(totalSz,[(pad,sz,off)])
type PadMask = (Int,[(Int,Int,Int)])
--Given a StructLayout, computes the bitlength of the padding before each field
--and adds the information to the layout.
--sz is the index of the leftmost bit from the right
getPadMask :: StructLayout -> PadMask
getPadMask (sz,szoffs) =
  (sz,go (sz+1) szoffs)
  where
    go _ [] = []
    go nextOff ((sz,off):szoffs) =
      (nextOff - (sz+off),sz,off) : go off szoffs

--Proposed syntax:
--{[align i] [pad i] [fieldNm =] v}
--Default: align byte, pad byte
--bitfield {a:n,b:m,...} could be sugar for a series of bit aligned and padded
--fields, a : UInt n, b : UInt m
--Why have a single, complex struct type rather than three types (tuple,
--struct and bitfield)?
--Because it allows you to create and access them with a single syntax, and
--also lets you flexibly mix alignment and padding as appropriate.
--Opt: field = 0 => mask it out; field = all 1s => or it
--Field |=, &= or ^= --convert to word op
