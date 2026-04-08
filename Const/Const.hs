{-# LANGUAGE LambdaCase, DeriveDataTypeable #-}
module Const.Const where

import AST.DTs

import Data.Generics (Data(..))
import Data.Char (intToDigit) --used for pretty show

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
  deriving (Eq,Ord,Read,Data)
--Giving Serialized a pretty show instance for debug:
instance Show Serialized where
  show = cc_showSerialized
--Copied from Pretty:
--(hex | label)* : sizeof
--We don't show len
cc_showSerialized :: Serialized -> String
cc_showSerialized ser =
  "["++ (serContent ser >>= showSerElem) ++ "]:" ++ show (serSizeof ser)
  where showSerElem :: SerElem -> String
        showSerElem = \case
          Left bytes -> bytes >>= showHex
          Right lab -> showLabel lab
        --If off == 0: lab:len
        --else: lab(off):len
        showLabel :: (Int,Int,String) -> String
        showLabel (off,len,lab) =
          lab ++ (if off /= 0 then "("++show off++")" else "") ++ ":" ++
          show len
        --Precondition: the b is in 0..255
        showHex b = map intToDigit [b `div` 16, b `mod` 16]
emptySer = Serialized 0 0 []
--Invariant: Content is in normal form, i.e. there are no adjacent [Int]
--regions, no empty [Int] regions nor zero-size labels.
type Content = [SerElem]
type SerElem = Either [Int] (Int,   --off
                          Int,   --len
                          String --label name
                         )
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

--A serialized function or global label; non-code global labels will be
--replaced with constants before Core optimization.
serLabel2 :: Name -> [T] -> Serialized
serLabel2 nm ts = Serialized {serLength = 2,
                              serSizeof = 2,
                              serContent = [Right (0,2,mkLabel nm ts)]
                             }

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

--A utility function used to compile EInteger in Fused.Monad.
--n larger than 2^256-1 is silently truncated.
--Precondition: n is non-negative
serWord :: Integer -> Serialized
serWord n
  | n < 0 = error $ "Compiler error: serWord expects non-negative n but got "
            ++ show n
  | let = let bs = reverse $ take 32 $ go n
              len = fromIntegral $ length bs
          in Serialized {serLength = len,
                         serSizeof = len,
                         serContent = [Left bs]
                        }
          where go = \case
                  0 -> []
                  n -> fromInteger (n `mod` 256) : go (n `div` 256)

--Split a Serialized with sizeof n into ceil(n/32) words; used for pushing
--constructor tags.
--Note length may be < sizeof, indicating Serialized contains a constructor
--smaller than the sizeof its type (e.g. Nil or Nothing).
--In that case, zero-valued right-padding words may be added.
--Bugfix: if sizeof ser % 32 /= 0, it's the first word that should be partial,
--not the last.
splitSer :: Serialized -> [Serialized]
splitSer ser = map stripZeroes $ splitPartial $ rightPadSer ser
  where splitPartial ser =
          let m = serSizeof ser `mod` 32
          in if m > 0
             then let (partial,whole) = takeDropSer m ser
                  in partial:splitWords whole
             else splitWords ser
        splitWords ser =
          if serSizeof ser == 0
          then []
          else let (w,rest) = takeDropSer 32 ser
               in w : splitWords rest
--Problem: serSizeof > serLength indicates right-padding, but stripZeroes
--removes left-padding zero bytes. That's OK for now since we'll just be
--pushing the Serialized, not concatenating it.
--TODO make two Serialized types with different invariants: a left-padded and
--right-padded version?
stripZeroes :: Serialized -> Serialized
stripZeroes ser =
  case serContent ser of
    Left bs : rest -> 
      let len = serLength ser
          bs' = dropWhile (==0) bs
          dropped = fromIntegral $ length $ takeWhile (==0) bs
      in Serialized {
        serLength = len - dropped,
        serSizeof = serSizeof ser, --irrelevant
        serContent = if null bs' then rest else Left bs' : rest
        }
    _ -> ser

--Precondition: serLength ser > len, len >= 0
--Splits ser into the first len bytes and the rest.
--Algo: while len > lengthContent of the next content, consume it and len-=lc.
--If len == 0, stop.
--Otherwise split the content and stop.
takeDropSer :: Integer -> Serialized -> (Serialized,Serialized)
takeDropSer len ser
  | serLength ser < len || len < 0 = error "takeDropSer precondition violated"
  | let = let (c1,c2) = go (fromInteger len) $ serContent ser
          in (Serialized {
                 serLength = len,
                 serSizeof = len,
                 serContent = normalizeContent c1
                 },
              Serialized {
                 serLength = serLength ser - len,
                 serSizeof = serLength ser - len,
                 serContent = normalizeContent c2
                 }
             )
          where go :: Int -> Content -> (Content,Content)
                go len cs
                  | len == 0 = ([],cs)
                  | c:cs' <- cs =
                      let lc = lengthContent c
                      in if len > lc
                         then let (prefix,suffix) = go (len-lc) cs'
                              in (c:prefix,suffix)
                         else let (prec,sufc) = splitContent len c
                              in ([prec],sufc:cs')
                  | let = error "len > serLength in takeDropSer!"

--The length of a single Content element (a label slice or bytestring)
lengthContent :: SerElem -> Int
lengthContent = \case
  Left bs -> length bs
  Right (_off,len,lab) -> len
--Precondition: the content's length >= len
splitContent :: Int -> SerElem -> (SerElem,SerElem)
splitContent len c
  | lengthContent c < len = error "len > length of content in splitContent!"
  | let = case c of
            Left bs -> (Left $ take len bs, Left $ drop len bs) 
            Right (off,lc,lab) ->
              (Right (off,len,lab), Right (off+len,lc-len,lab))

--Serialized is used to represent static bytestrings in code global initializers
--and DT tags, where the bytestring may be of length >32.
--However, when pushing a long constant it must be split into 32B words.
--The EVM ops PUSH0..PUSH32 have 0..32 bytes of immediate argument; they
--push their immediate argument as a 32B word left-padded with zero bytes.
--As such, it's inefficient to use 
