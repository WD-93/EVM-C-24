{-# LANGUAGE LambdaCase, DeriveDataTypeable #-}
module Const.Const where

import AST.DTs

import Data.Generics (Data(..))

--Just the pure functions from Const.Serialize

--Serialized values are more restricted than assembly, consisting only of
--Bytes [Int] or a sliced label. I therefore use a Serialized
--datatype to represent them instead of Asm.
--Why Integer length and not Int? Because otherwise
--null() :: UInt <very large number> will report an incorrect, potentially even
--negative, length.
data Serialized = Serialized {serLength :: Integer, --length in bytes
                              serSizeof :: Integer, --max length of type
                              serContent :: Content
                             }
  deriving (Eq,Ord,Read,Show,Data)
emptySer = Serialized 0 0 []
--Invariant: Content is in normal form, i.e. there are no adjacent [Int]
--regions, no empty [Int] regions nor zero-size labels.
type Content = [Either [Int] (Int,   --off
                              Int,   --len
                              String --label name
                             )]
--Quick-and-dirty solution: apply separate normalization function rather than
--merging it with concatenation and other ops.
normalizeContent :: Content -> Content
normalizeContent = go
  where go = \case
          [] -> []
          Left []:c -> go c
          --Empty label = ""
          Right (_off,0,_):c -> go c
          --label(off,len) ++ label(off+len,len') = label(off,len+len')
          Right (off,len,lab) : Right (off',len',lab') : c
            | off' == (off+len),
              lab' == lab ->
              go $ Right (off,len+len',lab) : c
          --O(n) because I'm repeatedly left-concatenating rather than
          --right-concatenating
          Left xs : c ->
            case go c of
              Left ys : c' -> Left (xs ++ ys) : c'
              c' -> Left xs : c'
          el : c -> el : go c

--When two serialized values are concatenated unboxed (either in an Array or
--unboxed constructor), each value is extended to its sizeof by zero-padding
--it to the right.
concatSer :: Serialized -> Serialized -> Serialized
concatSer s1 s2 =
  let s1' = rightPadSer s1
      s2' = rightPadSer s2
      len = serSizeof s1' + serSizeof s2'
  in Serialized {serLength = len,
                 serSizeof = len,
                 serContent = normalizeContent $ serContent s1 ++ serContent s2
                }
concatSers :: [Serialized] -> Serialized
concatSers = foldr concatSer emptySer

--If the serialized value is smaller than its type's maximum size
--(e.g. unboxed Nil or Nothing), pad to the right with zero bytes.
rightPadSer :: Serialized -> Serialized
rightPadSer s
  | serLength s > serSizeof s =
    error $ "Compiler error: serLength > serSizeof in " ++ show s
  | serLength s == serSizeof s = s
  | let diff = serSizeof s - serLength s =
          s{serLength = serSizeof s,
            serContent = normalizeContent $
                         serContent s ++ [Left $ replicate (fromInteger diff) 0]
           }

--Left-pad the value to a whole number of words; first extend it to max size.
--Ex: Nil :: List Memory Bool => 28B left-padding, 0x00, 3B right-padding.
leftPadSer :: Serialized -> Serialized
leftPadSer s =
  let s' = rightPadSer s
      sz = serSizeof s'
      paddedSz = sz `roundedUpMod` 32
      padRequired = paddedSz - sz
  in s'{serSizeof = paddedSz,
        serLength = paddedSz,
        serContent = normalizeContent $
                     Left (replicate (fromInteger padRequired) 0) :
                     serContent s'
       }
--The label format for functions and globals
mkLabel :: Name -> [T] -> String
mkLabel nm ts = nm ++ show ts

--Convert an Integer to an n-byte big-endian two's complement bytestring.
--Silently truncates if the number doesn't fit; TODO warn on precision loss.
--TODO deduplicate with existing Asm.integer2Bytes, though this one is more
--general (it handles > 32B).
--Note the programmer may select a ludicrous len
--TODO split up into fundamental funs. Note mod on a huge number is expensive...
serInt :: Integer -> Integer -> [Int]
serInt len k = paddedBs
  where modulus = 256 ^ len
        --Normalize k to k'' in the range 0..modulus-1
        k' = k `mod` modulus
        k'' = if k' < 0 then k' + modulus else k'
        n2rbs 0 = []
        n2rbs n = fromInteger (n `mod` 256) : n2rbs (n `div` 256)
        bs = reverse $ n2rbs k''
        paddedBs = replicate (fromInteger len - length bs) 0 ++ bs

--Serialized is used to represent static bytestrings in code global initializers
--and DT tags, where the bytestring may be of length >32.
--However, when pushing a long constant it must be split into 32B words.
--The EVM ops PUSH0..PUSH32 have 0..32 bytes of immediate argument; they
--push their immediate argument as a 32B word left-padded with zero bytes.
--As such, it's inefficient to use 
