{-# LANGUAGE LambdaCase #-}
module Construct where

import Data.Map (Map(..))
import qualified Data.Map as M
import Control.Monad.State

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
