{-# LANGUAGE LambdaCase #-}
module BuildStruct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Set (Set(..))
import qualified Data.Set as S
import Control.Monad.State
import Control.Arrow ((***))
import Data.List (sortOn)

--It's parameterized by input type so we can both debug and use it easily
--Debug parameter: (String,Int)
--Real: Name (used for vars in IR)
data O i = V (i,Int) --we tag with number of relevant bits
       | Shift (O i) Int --left shift, -ve is right shift
       | O i :|| O i
  deriving (Eq,Ord,Read)
instance Show i => Show (O i) where
  show (V (i,sz)) = show i ++ ":" ++ show sz
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
data Info = Bit | Byte | Word
  deriving (Eq,Ord,Read,Show)
info2Sz :: Info -> Int
info2Sz = \case
  Bit -> 1
  Byte -> 8
  Word -> 256
n `roundedUpMod` m = m * ((if (n `mod` m) > 1
                          then 1
                          else 0) + (n `div` m))

--Computes the layout of a struct.
--Arguments: [(padding info,alignment info, field value)]
--Result: output values of the struct
--Properties:
--There will be no empty words which solely consist of padding.
--Field words will be contiguous and non-overlapping.
--Each word of the input is included; no word is shifted to oblivion.

--Alignment i should add minimum padding to the last field to ensure this
--field starts at a multiple of info2Sz i.
--Padding i should add minimum padding to the current field to ensure the
--bitsize of the field + padding is a multiple of info2Sz i.
--Pad i of the next field does not render align i a noop, since the next field
--may start at an unaligned position.
buildStruct :: Ord i => [(Info,Info,Value i)] -> [O i]
buildStruct [] = []
buildStruct padalfs =
  --First, we replace the alignment info in each elem with the alignment of
  --its predecessor. Instead of Nothing, we use Bit for the first elem.
  --The alignment of the last field does nothing, but that's fine.
  let als = map (\(pad,al,f) -> al) padalfs
      predals = Bit : als --no need to call init here, zip handles that
      padalfs' = map (\(al,(pad,_,f)) -> (pad,al,f)) $ zip predals padalfs
      --Now we run the struct builder monad. For each field starting from the
      --last, we emit their size-tagged words in reverse order, then inc the
      --offset to account for their padding.
      ix2set = fst $ execState (mapM (\(pad,al,val@(sz,_)) -> do
                                   off <- gets snd
                                   let wszs = reverse $ tagWordsWithSize val
                                   mapM emitWord wszs
                                   --s <- get
                                   --error $ "Foo: " ++ show (s,wszs)
                                   incOff (computePad pad al sz off)) $
                                reverse padalfs')
               (M.empty,0)
      --Since M.elems outputs elems in ascending order, we must reverse
      sets = reverse $ M.elems ix2set
      --When building exprs, sort them by left-shift?
      exprs = map set2expr sets   
  in exprs
  where set2expr s =
          foldr1 (:||) $
          map (\(isz,lshift) -> V isz `shift` lshift) $
          sortOn (\(isz,lshift) -> negate lshift) $ S.toList s
--Given a field of size sz starting at offset off from the right,
--as well as the field's padding and the next field's alignment requirement,
--compute the number of padding bits.
computePad :: Info -> Info -> Int -> Int -> Int
computePad pad al sz off =
  let padBits = diff sz pad
      alBits = diff (sz+off) al
      diff n info = (n `roundedUpMod` info2Sz info) - n
  in max padBits alBits
  
--For well-formed Values (created with value), all but the first word will be
--256b and sz will match the number of words.
tagWordsWithSize :: Value i -> [(i,Int)]
tagWordsWithSize (0,[]) = []
tagWordsWithSize (sz,w:ws)
  | sz `mod` 256 > 0 = (w,sz`mod`256): map (\w -> (w,256)) ws
  | otherwise = map (\w -> (w,256)) (w:ws)
--Struct builder state:
--a map struct word (0-indexed, starting from the left) to size-tagged words
--with offsets,
--the current offset.
--Really you could use a list instead of a map, but why invite bugs?
type SB i = State (Map Int (Set ((i,Int),Int)), Int)
incOff :: Int -> SB i ()
incOff k = modify (id *** (+ k))
--The word is guaranteed to be added to the current struct word, but it may
--also overlap with the next, in which case it should be right-shifted and
--added to that as well.
--Note the word is guaranteed to have sz <= 256
emitWord :: Ord i => (i,Int) -> SB i ()
emitWord (i,sz) = do
  off <- gets snd
  let currWord = off `div` 256
      leftShift = off `mod` 256
  addShiftedWord currWord ((i,sz),leftShift)
  --The offset of the last included bit
  let lastIncludedBit = off + sz - 1
      --The index of the word it's included in
      highestWord = lastIncludedBit `div` 256
  if highestWord /= currWord
    then do
    let negRightShift = off `mod` 256 - 256
    addShiftedWord highestWord ((i,sz),negRightShift)
    else return ()
  incOff sz
addShiftedWord :: Ord i => Int -> ((i,Int),Int) -> SB i ()
addShiftedWord ix elem =
  modify (M.alter (\case Just s -> Just (S.insert elem s)
                         Nothing -> Just (S.singleton elem)
                  ) ix *** id)

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
