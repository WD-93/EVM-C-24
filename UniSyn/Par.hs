{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module UniSyn.Par where
import UniSyn.Abs
import UniSyn.Lex
import UniSyn.ErrM
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.11

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
newtype HappyWrap10 = HappyWrap10 (Ident)
happyIn10 :: (Ident) -> (HappyAbsSyn )
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap10 x)
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> HappyWrap10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
newtype HappyWrap11 = HappyWrap11 (Integer)
happyIn11 :: (Integer) -> (HappyAbsSyn )
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap11 x)
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> HappyWrap11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
newtype HappyWrap12 = HappyWrap12 (UIdent)
happyIn12 :: (UIdent) -> (HappyAbsSyn )
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap12 x)
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> HappyWrap12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
newtype HappyWrap13 = HappyWrap13 (D)
happyIn13 :: (D) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap13 x)
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> HappyWrap13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
newtype HappyWrap14 = HappyWrap14 ([S])
happyIn14 :: ([S]) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap14 x)
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> HappyWrap14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
newtype HappyWrap15 = HappyWrap15 (S)
happyIn15 :: (S) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap15 x)
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> HappyWrap15
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
newtype HappyWrap16 = HappyWrap16 (E)
happyIn16 :: (E) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap16 x)
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> HappyWrap16
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
newtype HappyWrap17 = HappyWrap17 ([E])
happyIn17 :: ([E]) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap17 x)
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> HappyWrap17
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
newtype HappyWrap18 = HappyWrap18 (E)
happyIn18 :: (E) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap18 x)
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> HappyWrap18
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
newtype HappyWrap19 = HappyWrap19 (E)
happyIn19 :: (E) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap19 x)
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> HappyWrap19
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x00\x02\x00\x00\x81\xdf\x01\x00\x20\xf0\x3b\x00\x00\x04\x00\x07\x00\x80\x00\xe0\x00\x00\x10\x00\x1c\x00\x00\x02\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x38\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\xc0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x20\xf0\x3b\x00\x00\x04\x00\x00\x00\x80\x00\xe0\x00\x00\x10\x00\x00\x00\x00\x02\xbf\x03\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x09\xc0\x01\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x80\x00\xe0\x00\x00\x10\xf8\x1d\x00\x00\x00\x40\x00\x00\x40\x00\x70\x00\x00\x00\x00\x00\x00\x00\x01\xc0\x01\x00\x00\x00\x00\x00\x00\x04\x00\x07\x00\x80\x00\xe0\x00\x00\x60\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\xc0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x20\xf0\x3b\x00\x00\x04\x7e\x07\x00\x80\xc0\xef\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pD","%start_pListS","%start_pS","%start_pE1","%start_pListE","%start_pE","%start_pE2","Ident","Integer","UIdent","D","ListS","S","E1","ListE","E","E2","'('","')'","','","':'","':='","';'","'='","'S'","'else'","'if'","'return'","'while'","'{'","'}'","L_ident","L_integ","L_UIdent","%eof"]
        bit_start = st * 37
        bit_end = (st + 1) * 37
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..36]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\xf5\xff\x13\x00\x31\x00\x3e\x00\x3e\x00\x3e\x00\x19\x00\x17\x00\x00\x00\x15\x00\x3e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x15\x00\x00\x00\x06\x00\x00\x00\x00\x00\x15\x00\x30\x00\x22\x00\x22\x00\x2f\x00\x00\x00\x31\x00\x36\x00\x3e\x00\x45\x00\x20\x00\x35\x00\x42\x00\x34\x00\x35\x00\x44\x00\x3e\x00\x01\x00\x3c\x00\x3e\x00\x00\x00\x3e\x00\x00\x00\x3e\x00\x3e\x00\x16\x00\x00\x00\x49\x00\x00\x00\x3e\x00\x00\x00\x00\x00\x4a\x00\x56\x00\x00\x00\xf3\xff\x00\x00\x4c\x00\x20\x00\x31\x00\x31\x00\x5c\x00\x00\x00\x00\x00\x00\x00\x52\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x03\x00\x51\x00\x97\x00\x0f\x01\x5b\x00\xa1\x00\x5f\x00\x00\x00\x00\x00\x00\x00\xab\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xbf\x00\x00\x00\xc9\x00\x00\x00\x65\x00\x00\x00\x00\x00\x19\x01\x00\x00\x00\x00\xd3\x00\x6f\x00\x00\x00\xdd\x00\x00\x00\xe7\x00\x00\x00\xf1\x00\x79\x00\x00\x00\x00\x00\x00\x00\x00\x00\x83\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8d\x00\xfb\x00\x05\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\xf0\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf8\xff\x00\x00\x00\x00\xe5\xff\xe6\xff\xe4\xff\xde\xff\x00\x00\xe1\xff\x00\x00\xf7\xff\xf6\xff\x00\x00\xe0\xff\x00\x00\x00\x00\x00\x00\xed\xff\x00\x00\x00\x00\x00\x00\x00\x00\xf0\xff\x00\x00\xef\xff\x00\x00\x00\x00\x00\x00\x00\x00\xf0\xff\x00\x00\x00\x00\xeb\xff\x00\x00\xe9\xff\x00\x00\x00\x00\x00\x00\xe3\xff\x00\x00\xdd\xff\x00\x00\xdf\xff\xec\xff\x00\x00\x00\x00\xe7\xff\xee\xff\xf5\xff\x00\x00\xf0\xff\x00\x00\x00\x00\x00\x00\xe2\xff\xea\xff\xe8\xff\x00\x00\xf4\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x0e\x00\x01\x00\x00\x00\x0f\x00\x12\x00\x03\x00\x01\x00\x02\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x01\x00\x0f\x00\x10\x00\x11\x00\x02\x00\x03\x00\x01\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x01\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x0f\x00\x12\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x01\x00\x03\x00\x12\x00\x01\x00\x07\x00\x01\x00\x04\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x01\x00\x0f\x00\x10\x00\x11\x00\x0f\x00\x10\x00\x11\x00\x01\x00\x12\x00\x06\x00\x05\x00\x0e\x00\x02\x00\x02\x00\x0f\x00\x10\x00\x11\x00\x0e\x00\x00\x00\x01\x00\x02\x00\x12\x00\x04\x00\x05\x00\x06\x00\x02\x00\x0d\x00\x09\x00\x00\x00\x01\x00\x02\x00\x02\x00\xff\xff\x0e\x00\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\x09\x00\x04\x00\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\x04\x00\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\x07\x00\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\x04\x00\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\x08\x00\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\x05\x00\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\xff\xff\x09\x00\x00\x00\x01\x00\x02\x00\xff\xff\xff\xff\xff\xff\x06\x00\xff\xff\xff\xff\x09\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\xee\xff\x12\x00\x21\x00\x09\x00\xee\xff\x22\x00\x12\x00\x2f\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\xf0\xff\x09\x00\x13\x00\x14\x00\xf0\xff\x12\x00\x09\x00\x13\x00\x14\x00\x31\x00\x32\x00\x0b\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x12\x00\x09\x00\x13\x00\x14\x00\xf0\xff\x09\x00\xff\xff\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\xf0\xff\x09\x00\x13\x00\x14\x00\x12\x00\x2d\x00\xff\xff\x12\x00\x2c\x00\x2a\x00\x25\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x12\x00\x09\x00\x13\x00\x14\x00\x09\x00\x13\x00\x14\x00\x28\x00\xff\xff\x26\x00\x3a\x00\x37\x00\x31\x00\x3d\x00\x09\x00\x13\x00\x14\x00\xef\xff\x0b\x00\x0c\x00\x0d\x00\xef\xff\x1f\x00\x20\x00\x18\x00\x3c\x00\x3b\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x3f\x00\x00\x00\x43\x00\x0e\x00\x14\x00\x15\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x09\x00\x26\x00\x20\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x37\x00\x20\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x32\x00\x15\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x3d\x00\x15\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x41\x00\x20\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x17\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x0f\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x2f\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x2d\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x2a\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x28\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x38\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x35\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x34\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x0e\x00\x00\x00\x33\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x40\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x3f\x00\x18\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x16\x00\x00\x00\x00\x00\x10\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x00\x00\x00\x00\x23\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (7, 34) [
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34)
	]

happy_n_terms = 19 :: Int
happy_n_nonterms = 10 :: Int

happyReduce_7 = happySpecReduce_1  0# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn10
		 (Ident happy_var_1
	)}

happyReduce_8 = happySpecReduce_1  1# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn11
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_9 = happySpecReduce_1  2# happyReduction_9
happyReduction_9 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (T_UIdent happy_var_1)) -> 
	happyIn12
		 (UIdent (happy_var_1)
	)}

happyReduce_10 = happySpecReduce_3  3# happyReduction_10
happyReduction_10 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn13
		 (UniSyn.Abs.TySig happy_var_1 happy_var_3
	)}}

happyReduce_11 = happyReduce 6# 3# happyReduction_11
happyReduction_11 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	case happyOut16 happy_x_2 of { (HappyWrap16 happy_var_2) -> 
	case happyOut14 happy_x_5 of { (HappyWrap14 happy_var_5) -> 
	happyIn13
		 (UniSyn.Abs.Defun happy_var_1 happy_var_2 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_12 = happySpecReduce_0  4# happyReduction_12
happyReduction_12  =  happyIn14
		 ([]
	)

happyReduce_13 = happySpecReduce_1  4# happyReduction_13
happyReduction_13 happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	happyIn14
		 ((:[]) happy_var_1
	)}

happyReduce_14 = happySpecReduce_3  4# happyReduction_14
happyReduction_14 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	case happyOut14 happy_x_3 of { (HappyWrap14 happy_var_3) -> 
	happyIn14
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_15 = happySpecReduce_0  4# happyReduction_15
happyReduction_15  =  happyIn14
		 ([]
	)

happyReduce_16 = happySpecReduce_1  4# happyReduction_16
happyReduction_16 happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	happyIn14
		 ((:[]) happy_var_1
	)}

happyReduce_17 = happySpecReduce_3  4# happyReduction_17
happyReduction_17 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_1 of { (HappyWrap15 happy_var_1) -> 
	case happyOut14 happy_x_3 of { (HappyWrap14 happy_var_3) -> 
	happyIn14
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_18 = happySpecReduce_1  5# happyReduction_18
happyReduction_18 happy_x_1
	 =  happyIn15
		 (UniSyn.Abs.PlaceholderS
	)

happyReduce_19 = happySpecReduce_3  5# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_1 of { (HappyWrap16 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn15
		 (UniSyn.Abs.Assign happy_var_1 happy_var_3
	)}}

happyReduce_20 = happySpecReduce_2  5# happyReduction_20
happyReduction_20 happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	happyIn15
		 (UniSyn.Abs.Return happy_var_2
	)}

happyReduce_21 = happyReduce 5# 5# happyReduction_21
happyReduction_21 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	case happyOut15 happy_x_5 of { (HappyWrap15 happy_var_5) -> 
	happyIn15
		 (UniSyn.Abs.If happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_22 = happySpecReduce_2  5# happyReduction_22
happyReduction_22 happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_2 of { (HappyWrap15 happy_var_2) -> 
	happyIn15
		 (UniSyn.Abs.Else happy_var_2
	)}

happyReduce_23 = happyReduce 5# 5# happyReduction_23
happyReduction_23 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	case happyOut15 happy_x_5 of { (HappyWrap15 happy_var_5) -> 
	happyIn15
		 (UniSyn.Abs.While happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_24 = happySpecReduce_3  5# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_2 of { (HappyWrap14 happy_var_2) -> 
	happyIn15
		 (UniSyn.Abs.Do happy_var_2
	)}

happyReduce_25 = happySpecReduce_1  6# happyReduction_25
happyReduction_25 happy_x_1
	 =  case happyOut11 happy_x_1 of { (HappyWrap11 happy_var_1) -> 
	happyIn16
		 (UniSyn.Abs.EInt happy_var_1
	)}

happyReduce_26 = happySpecReduce_1  6# happyReduction_26
happyReduction_26 happy_x_1
	 =  case happyOut10 happy_x_1 of { (HappyWrap10 happy_var_1) -> 
	happyIn16
		 (UniSyn.Abs.EVar happy_var_1
	)}

happyReduce_27 = happySpecReduce_1  6# happyReduction_27
happyReduction_27 happy_x_1
	 =  case happyOut12 happy_x_1 of { (HappyWrap12 happy_var_1) -> 
	happyIn16
		 (UniSyn.Abs.ECon happy_var_1
	)}

happyReduce_28 = happySpecReduce_2  6# happyReduction_28
happyReduction_28 happy_x_2
	happy_x_1
	 =  happyIn16
		 (UniSyn.Abs.EEmptyTup
	)

happyReduce_29 = happyReduce 5# 6# happyReduction_29
happyReduction_29 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	case happyOut17 happy_x_4 of { (HappyWrap17 happy_var_4) -> 
	happyIn16
		 (UniSyn.Abs.ETup happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_30 = happySpecReduce_1  6# happyReduction_30
happyReduction_30 happy_x_1
	 =  case happyOut19 happy_x_1 of { (HappyWrap19 happy_var_1) -> 
	happyIn16
		 (happy_var_1
	)}

happyReduce_31 = happySpecReduce_1  7# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	happyIn17
		 ((:[]) happy_var_1
	)}

happyReduce_32 = happySpecReduce_3  7# happyReduction_32
happyReduction_32 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut17 happy_x_3 of { (HappyWrap17 happy_var_3) -> 
	happyIn17
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_33 = happySpecReduce_1  8# happyReduction_33
happyReduction_33 happy_x_1
	 =  case happyOut16 happy_x_1 of { (HappyWrap16 happy_var_1) -> 
	happyIn18
		 (happy_var_1
	)}

happyReduce_34 = happySpecReduce_3  9# happyReduction_34
happyReduction_34 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	happyIn19
		 (happy_var_2
	)}

happyNewToken action sts stk [] =
	happyDoAction 18# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TV happy_dollar_dollar) -> cont 15#;
	PT _ (TI happy_dollar_dollar) -> cont 16#;
	PT _ (T_UIdent happy_dollar_dollar) -> cont 17#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 18# tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => ([(Token)], [String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pD tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (let {(HappyWrap13 x') = happyOut13 x} in x'))

pListS tks = happySomeParser where
 happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (let {(HappyWrap14 x') = happyOut14 x} in x'))

pS tks = happySomeParser where
 happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (let {(HappyWrap15 x') = happyOut15 x} in x'))

pE1 tks = happySomeParser where
 happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (let {(HappyWrap16 x') = happyOut16 x} in x'))

pListE tks = happySomeParser where
 happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (let {(HappyWrap17 x') = happyOut17 x} in x'))

pE tks = happySomeParser where
 happySomeParser = happyThen (happyParse 5# tks) (\x -> happyReturn (let {(HappyWrap18 x') = happyOut18 x} in x'))

pE2 tks = happySomeParser where
 happySomeParser = happyThen (happyParse 6# tks) (\x -> happyReturn (let {(HappyWrap19 x') = happyOut19 x} in x'))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 10 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4











































{-# LINE 10 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}















{-# LINE 10 "<command-line>" #-}
{-# LINE 1 "/tmp/ghc8371_0/ghc_2.h" #-}
































































































































































































{-# LINE 10 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif
{-# LINE 43 "templates/GenericTemplate.hs" #-}

data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList







{-# LINE 65 "templates/GenericTemplate.hs" #-}

{-# LINE 75 "templates/GenericTemplate.hs" #-}

{-# LINE 84 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}


          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}


                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+#  i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 180 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+#  nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+#  nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
