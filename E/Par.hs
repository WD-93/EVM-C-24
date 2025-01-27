{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module E.Par where
import E.Abs
import E.Lex
import E.ErrM
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
newtype HappyWrap18 = HappyWrap18 (Ident)
happyIn18 :: (Ident) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap18 x)
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> HappyWrap18
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
newtype HappyWrap19 = HappyWrap19 (Integer)
happyIn19 :: (Integer) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap19 x)
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> HappyWrap19
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
newtype HappyWrap20 = HappyWrap20 (UIdent)
happyIn20 :: (UIdent) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap20 x)
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> HappyWrap20
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
newtype HappyWrap21 = HappyWrap21 (Infix)
happyIn21 :: (Infix) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap21 x)
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> HappyWrap21
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
newtype HappyWrap22 = HappyWrap22 (M)
happyIn22 :: (M) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap22 x)
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> HappyWrap22
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
newtype HappyWrap23 = HappyWrap23 ([D])
happyIn23 :: ([D]) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap23 x)
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> HappyWrap23
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
newtype HappyWrap24 = HappyWrap24 (D)
happyIn24 :: (D) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap24 x)
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> HappyWrap24
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
newtype HappyWrap25 = HappyWrap25 (ConArgs)
happyIn25 :: (ConArgs) -> (HappyAbsSyn )
happyIn25 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap25 x)
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> HappyWrap25
happyOut25 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut25 #-}
newtype HappyWrap26 = HappyWrap26 (S)
happyIn26 :: (S) -> (HappyAbsSyn )
happyIn26 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap26 x)
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> HappyWrap26
happyOut26 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut26 #-}
newtype HappyWrap27 = HappyWrap27 ([S])
happyIn27 :: ([S]) -> (HappyAbsSyn )
happyIn27 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap27 x)
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> HappyWrap27
happyOut27 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut27 #-}
newtype HappyWrap28 = HappyWrap28 (E)
happyIn28 :: (E) -> (HappyAbsSyn )
happyIn28 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap28 x)
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> HappyWrap28
happyOut28 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut28 #-}
newtype HappyWrap29 = HappyWrap29 (E)
happyIn29 :: (E) -> (HappyAbsSyn )
happyIn29 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap29 x)
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> HappyWrap29
happyOut29 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut29 #-}
newtype HappyWrap30 = HappyWrap30 (E)
happyIn30 :: (E) -> (HappyAbsSyn )
happyIn30 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap30 x)
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> HappyWrap30
happyOut30 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut30 #-}
newtype HappyWrap31 = HappyWrap31 (E)
happyIn31 :: (E) -> (HappyAbsSyn )
happyIn31 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap31 x)
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> HappyWrap31
happyOut31 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut31 #-}
newtype HappyWrap32 = HappyWrap32 ([E])
happyIn32 :: ([E]) -> (HappyAbsSyn )
happyIn32 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap32 x)
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> HappyWrap32
happyOut32 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut32 #-}
newtype HappyWrap33 = HappyWrap33 ([Field])
happyIn33 :: ([Field]) -> (HappyAbsSyn )
happyIn33 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap33 x)
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> HappyWrap33
happyOut33 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut33 #-}
newtype HappyWrap34 = HappyWrap34 (OS)
happyIn34 :: (OS) -> (HappyAbsSyn )
happyIn34 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap34 x)
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> HappyWrap34
happyOut34 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut34 #-}
newtype HappyWrap35 = HappyWrap35 (Field)
happyIn35 :: (Field) -> (HappyAbsSyn )
happyIn35 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap35 x)
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> HappyWrap35
happyOut35 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut35 #-}
newtype HappyWrap36 = HappyWrap36 (PadInfo)
happyIn36 :: (PadInfo) -> (HappyAbsSyn )
happyIn36 x = Happy_GHC_Exts.unsafeCoerce# (HappyWrap36 x)
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> HappyWrap36
happyOut36 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x84\x00\x00\x00\x00\x00\x00\x00\x10\x02\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x10\x10\x49\xea\x01\x00\x00\x00\x40\x40\x24\xa9\x07\x00\x00\x00\x00\x01\x01\x80\x1e\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x10\x10\x00\xe8\x00\x00\x00\x00\x40\x40\x00\xa0\x03\x00\x00\x00\x00\x01\x01\x80\x1e\x00\x00\x00\x00\x04\x0c\x08\x7a\x00\x00\x00\x00\x10\x10\x00\xe8\x00\x00\x00\x00\x40\xc0\x80\xa0\x07\x00\x00\x00\x00\x00\x0c\x40\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x10\x00\xe8\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x80\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x01\x80\x1e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x00\x04\x00\x00\x00\x00\x00\x00\x03\x10\x00\x00\x00\x00\x00\x01\x03\x82\x1f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x04\x04\x00\x3a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x01\x01\x80\x1e\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x10\x11\x00\xe8\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x40\x08\x00\x00\x00\x00\x00\x00\x00\x21\x00\x00\x00\x00\x00\x20\x00\x80\x00\x00\x00\x00\x00\x28\x00\x00\x00\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x40\x00\xa0\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x10\x10\x49\xea\x01\x00\x00\x00\x40\x40\x24\xa9\x07\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x10\x10\x00\xe8\x01\x00\x00\x00\x40\xc0\x80\xa0\x07\x00\x00\x00\x00\x01\x01\x80\x0e\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\xc0\x80\xa0\x07\x00\x00\x00\x00\x01\x03\x82\x1e\x00\x00\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x40\x00\xa0\x07\x00\x00\x00\x00\x01\x01\x80\x0e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x10\x00\xe8\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x40\x00\xa0\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x04\x44\x92\x7a\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x91\xa4\x1e\x00\x00\x00\x00\x04\x04\x00\x7a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x40\x24\xa9\x07\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x91\xa4\x1e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pM","%start_pListD","%start_pD","%start_pConArgs","%start_pS","%start_pListS","%start_pE","%start_pE1","%start_pE2","%start_pE3","%start_pListE","%start_pListField","%start_pOS","%start_pField","%start_pPadInfo","Ident","Integer","UIdent","Infix","M","ListD","D","ConArgs","S","ListS","E","E1","E2","E3","ListE","ListField","OS","Field","PadInfo","'('","')'","','","'.'","':'","':='","';'","'='","'_'","'align'","'bit'","'byte'","'do'","'else'","'end'","'if'","'module'","'pad'","'return'","'then'","'type'","'while'","'word'","'{'","'}'","L_ident","L_integ","L_UIdent","L_Infix","%eof"]
        bit_start = st * 66
        bit_end = (st + 1) * 66
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..65]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\xfc\xff\x10\x00\x10\x00\x1a\x00\x11\x00\x11\x00\x3d\x00\x3d\x00\x55\x00\x55\x00\x3d\x00\x33\x00\x55\x00\x33\x00\x67\x00\xfb\xff\x00\x00\x2a\x00\x00\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x3d\x00\x00\x00\x00\x00\x3d\x00\x2b\x00\x4b\x00\x48\x00\x00\x00\x67\x00\x67\x00\x27\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3d\x00\x68\x00\x58\x00\x58\x00\x83\x00\x85\x00\x71\x00\x02\x00\x01\x00\x71\x00\x71\x00\x89\x00\x73\x00\x00\x00\x7b\x00\x3d\x00\x3d\x00\x97\x00\x7c\x00\x00\x00\x74\x00\x65\x00\x7c\x00\x84\x00\x86\x00\x9a\x00\x87\x00\x8b\x00\x10\x00\x10\x00\xf9\xff\x08\x00\x3d\x00\x00\x00\x3d\x00\x00\x00\x8e\x00\x11\x00\x11\x00\xa6\x00\x92\x00\x3d\x00\x33\x00\x55\x00\x99\x00\x00\x00\x33\x00\x33\x00\x72\x00\x00\x00\x3d\x00\x55\x00\x00\x00\x3d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9b\x00\x11\x00\xb1\x00\x00\x00\x11\x00\x3d\x00\x00\x00\x9d\x00\x00\x00\x00\x00\x00\x00\x11\x00\xa7\x00\x00\x00\xb5\x00\x00\x00\x11\x00\x00\x00\xb6\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\xc2\x00\x32\x00\x0b\x00\x45\x00\x36\x01\x0c\x01\x72\x01\xba\x01\x03\x00\x07\x00\xe9\x00\x78\x00\x16\x00\xae\x00\xb2\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc8\x01\x00\x00\x00\x00\x03\x01\x00\x00\x00\x00\x80\x01\x00\x00\xbd\x00\xbe\x00\x8a\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x52\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x84\x01\x92\x01\x00\x00\x00\x00\x00\x00\xc7\x00\xbc\x00\x00\x00\x75\x00\x00\x00\x00\x00\x00\x00\x00\x00\x35\x00\xdb\x00\xc7\x00\x00\x00\x96\x01\x00\x00\xa4\x01\x00\x00\x00\x00\x1a\x01\x28\x01\x00\x00\xc8\x00\xee\x00\x9c\x00\x5b\x00\x00\x00\x00\x00\xc0\x00\xd2\x00\x00\x00\x00\x00\xcc\x01\xd8\x00\x00\x00\xa8\x01\x00\x00\x00\x00\x00\x00\x00\x00\xfd\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x44\x01\x00\x00\x00\x00\x52\x01\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x01\x00\x00\x00\x00\x00\x00\x00\x00\x6e\x01\x00\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\xeb\xff\x00\x00\x00\x00\x00\x00\xde\xff\x00\x00\x00\x00\x00\x00\x00\x00\xca\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf0\xff\x00\x00\xbf\xff\xbe\xff\xbd\xff\xd4\xff\xd1\xff\xd3\xff\x00\x00\xc0\xff\xda\xff\xd7\xff\xd5\xff\x00\x00\x00\x00\xcc\xff\x00\x00\x00\x00\x00\x00\xef\xff\xee\xff\xed\xff\xd4\xff\xc5\xff\xd5\xff\x00\x00\x00\x00\xc7\xff\xc9\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xdd\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe5\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xea\xff\x00\x00\x00\x00\xeb\xff\xeb\xff\x00\x00\x00\x00\x00\x00\xe4\xff\x00\x00\xe0\xff\x00\x00\xde\xff\xde\xff\xd6\xff\x00\x00\xca\xff\x00\x00\x00\x00\x00\x00\xce\xff\x00\x00\x00\x00\x00\x00\xd0\xff\x00\x00\x00\x00\xd8\xff\x00\x00\xc1\xff\xd9\xff\xdb\xff\xcb\xff\xca\xff\xc2\xff\xc3\xff\xcd\xff\xc4\xff\xc6\xff\xc8\xff\xd2\xff\xdc\xff\x00\x00\x00\x00\x00\x00\xe7\xff\x00\x00\x00\x00\xe9\xff\x00\x00\xec\xff\xe6\xff\xe8\xff\x00\x00\x00\x00\xdf\xff\x00\x00\xcf\xff\x00\x00\xe1\xff\x00\x00\xe2\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x08\x00\x01\x00\x00\x00\x01\x00\x02\x00\x04\x00\x00\x00\x01\x00\x02\x00\x09\x00\x00\x00\x04\x00\x11\x00\x06\x00\x0c\x00\x0d\x00\x06\x00\x01\x00\x1a\x00\x0d\x00\x1a\x00\x00\x00\x01\x00\x02\x00\x18\x00\x09\x00\x1a\x00\x1b\x00\x1c\x00\x0d\x00\x1e\x00\x1e\x00\x10\x00\x0c\x00\x0d\x00\x13\x00\x15\x00\x10\x00\x16\x00\x01\x00\x18\x00\x1a\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x04\x00\x09\x00\x0a\x00\x00\x00\x08\x00\x01\x00\x00\x00\x1c\x00\x05\x00\x06\x00\x12\x00\x05\x00\x06\x00\x09\x00\x0a\x00\x01\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x12\x00\x09\x00\x02\x00\x1e\x00\x01\x00\x02\x00\x18\x00\x07\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x09\x00\x00\x00\x01\x00\x02\x00\x18\x00\x01\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x00\x00\x01\x00\x02\x00\x09\x00\x0d\x00\x18\x00\x05\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x01\x00\x0c\x00\x0d\x00\x1e\x00\x05\x00\x10\x00\x04\x00\x18\x00\x09\x00\x1a\x00\x1b\x00\x1c\x00\x0b\x00\x0c\x00\x02\x00\x03\x00\x1e\x00\x02\x00\x00\x00\x01\x00\x02\x00\x03\x00\x07\x00\x18\x00\x17\x00\x1a\x00\x1b\x00\x1c\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x03\x00\x0f\x00\x03\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x1a\x00\x1e\x00\x07\x00\x1e\x00\x1e\x00\x18\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x01\x00\x0f\x00\x1e\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x1c\x00\x07\x00\x14\x00\x18\x00\x1e\x00\x1e\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x04\x00\x0f\x00\x1a\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x19\x00\x02\x00\x19\x00\x0e\x00\x19\x00\x02\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x12\x00\x0f\x00\x04\x00\x00\x00\x00\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\xff\xff\x12\x00\x12\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x00\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x05\x00\x06\x00\xff\xff\x11\x00\x0c\x00\x0d\x00\xff\xff\xff\xff\x10\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x00\x00\x01\x00\x02\x00\x03\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x00\x00\x01\x00\x02\x00\x03\x00\x0d\x00\xff\xff\xff\xff\xff\xff\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\x08\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\x08\x00\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\x0a\x00\x0b\x00\x0c\x00\x0d\x00\xff\xff\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\x0b\x00\x0c\x00\x0d\x00\xff\xff\x0b\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x0d\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x70\x00\x1f\x00\x26\x00\x16\x00\x17\x00\x50\x00\x26\x00\x16\x00\x17\x00\x20\x00\x3c\x00\x50\x00\x43\x00\x6f\x00\x2f\x00\x28\x00\x3d\x00\x1f\x00\x11\x00\x2e\x00\x11\x00\x26\x00\x16\x00\x17\x00\x23\x00\x20\x00\x11\x00\x24\x00\x25\x00\x36\x00\xff\xff\xff\xff\x37\x00\x27\x00\x28\x00\x38\x00\x3f\x00\x29\x00\x39\x00\x1f\x00\x23\x00\x11\x00\x11\x00\x24\x00\x25\x00\x26\x00\x50\x00\x20\x00\x21\x00\x3c\x00\x5a\x00\x1f\x00\x3c\x00\x25\x00\x3f\x00\x40\x00\x22\x00\x71\x00\x40\x00\x20\x00\x21\x00\x1f\x00\x23\x00\x55\x00\x11\x00\x24\x00\x25\x00\x26\x00\x22\x00\x20\x00\x3a\x00\xff\xff\x1f\x00\x59\x00\x23\x00\x3b\x00\x11\x00\x24\x00\x25\x00\x26\x00\x20\x00\x26\x00\x16\x00\x17\x00\x23\x00\x1f\x00\x11\x00\x24\x00\x25\x00\x26\x00\x26\x00\x16\x00\x17\x00\x20\x00\x4e\x00\x23\x00\x5d\x00\x11\x00\x24\x00\x25\x00\x26\x00\x1f\x00\x27\x00\x28\x00\xff\xff\x48\x00\x65\x00\x50\x00\x23\x00\x20\x00\x11\x00\x24\x00\x25\x00\x13\x00\x14\x00\x61\x00\x62\x00\xff\xff\x3a\x00\x15\x00\x16\x00\x17\x00\x18\x00\x45\x00\x23\x00\x15\x00\x11\x00\x24\x00\x25\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x52\x00\x2a\x00\x51\x00\x2b\x00\x15\x00\x16\x00\x17\x00\x18\x00\x11\x00\xff\xff\x4e\x00\xff\xff\xff\xff\x4d\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x4a\x00\x53\x00\xff\xff\x2b\x00\x15\x00\x16\x00\x17\x00\x18\x00\x25\x00\x45\x00\x6c\x00\x44\x00\xff\xff\xff\xff\x19\x00\x1a\x00\x1b\x00\x1c\x00\x50\x00\x66\x00\x11\x00\x2b\x00\x15\x00\x16\x00\x17\x00\x18\x00\x65\x00\x76\x00\x78\x00\x7b\x00\x73\x00\x7a\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x1d\x00\x15\x00\x16\x00\x17\x00\x18\x00\x11\x00\x7e\x00\x41\x00\x48\x00\x68\x00\x46\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x00\x00\x56\x00\x55\x00\x63\x00\x15\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x26\x00\x16\x00\x17\x00\x3c\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x70\x00\x40\x00\x00\x00\x62\x00\x27\x00\x28\x00\x00\x00\x00\x00\x5e\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x2c\x00\x1a\x00\x1b\x00\x1c\x00\x2d\x00\x2c\x00\x1a\x00\x1b\x00\x1c\x00\x67\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x26\x00\x16\x00\x17\x00\x5a\x00\x2c\x00\x1a\x00\x1b\x00\x1c\x00\x78\x00\x26\x00\x16\x00\x17\x00\x18\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x32\x00\x33\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x32\x00\x6a\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x32\x00\x69\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x39\x00\x00\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x76\x00\x00\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x74\x00\x00\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7b\x00\x00\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x7c\x00\x00\x00\x34\x00\x1a\x00\x1b\x00\x1c\x00\x31\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x57\x00\x1a\x00\x1b\x00\x1c\x00\x4b\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x4a\x00\x1a\x00\x1b\x00\x1c\x00\x6d\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x6c\x00\x1a\x00\x1b\x00\x1c\x00\x5d\x00\x1a\x00\x1b\x00\x1c\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x73\x00\x1a\x00\x1b\x00\x1c\x00\x00\x00\x30\x00\x1b\x00\x28\x00\x26\x00\x16\x00\x17\x00\x18\x00\x26\x00\x16\x00\x17\x00\x18\x00\x00\x00\x00\x00\x00\x00\x5b\x00\x1b\x00\x28\x00\x00\x00\x5f\x00\x1b\x00\x28\x00\x26\x00\x16\x00\x17\x00\x52\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (15, 66) [
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
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66)
	]

happy_n_terms = 31 :: Int
happy_n_nonterms = 19 :: Int

happyReduce_15 = happySpecReduce_1  0# happyReduction_15
happyReduction_15 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn18
		 (Ident happy_var_1
	)}

happyReduce_16 = happySpecReduce_1  1# happyReduction_16
happyReduction_16 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn19
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_17 = happySpecReduce_1  2# happyReduction_17
happyReduction_17 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (T_UIdent happy_var_1)) -> 
	happyIn20
		 (UIdent (happy_var_1)
	)}

happyReduce_18 = happySpecReduce_1  3# happyReduction_18
happyReduction_18 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (T_Infix happy_var_1)) -> 
	happyIn21
		 (Infix (happy_var_1)
	)}

happyReduce_19 = happyReduce 4# 4# happyReduction_19
happyReduction_19 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut23 happy_x_3 of { (HappyWrap23 happy_var_3) -> 
	happyIn22
		 (E.Abs.Module happy_var_3
	) `HappyStk` happyRest}

happyReduce_20 = happySpecReduce_0  5# happyReduction_20
happyReduction_20  =  happyIn23
		 ([]
	)

happyReduce_21 = happySpecReduce_1  5# happyReduction_21
happyReduction_21 happy_x_1
	 =  case happyOut24 happy_x_1 of { (HappyWrap24 happy_var_1) -> 
	happyIn23
		 ((:[]) happy_var_1
	)}

happyReduce_22 = happySpecReduce_3  5# happyReduction_22
happyReduction_22 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_1 of { (HappyWrap24 happy_var_1) -> 
	case happyOut23 happy_x_3 of { (HappyWrap23 happy_var_3) -> 
	happyIn23
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_23 = happyReduce 4# 6# happyReduction_23
happyReduction_23 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut31 happy_x_2 of { (HappyWrap31 happy_var_2) -> 
	case happyOut26 happy_x_4 of { (HappyWrap26 happy_var_4) -> 
	happyIn24
		 (E.Abs.Defun happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_24 = happySpecReduce_3  6# happyReduction_24
happyReduction_24 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut28 happy_x_3 of { (HappyWrap28 happy_var_3) -> 
	happyIn24
		 (E.Abs.TySig happy_var_1 happy_var_3
	)}}

happyReduce_25 = happyReduce 4# 6# happyReduction_25
happyReduction_25 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut25 happy_x_2 of { (HappyWrap25 happy_var_2) -> 
	case happyOut28 happy_x_4 of { (HappyWrap28 happy_var_4) -> 
	happyIn24
		 (E.Abs.TySyn happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_26 = happySpecReduce_1  7# happyReduction_26
happyReduction_26 happy_x_1
	 =  case happyOut20 happy_x_1 of { (HappyWrap20 happy_var_1) -> 
	happyIn25
		 (E.Abs.CANil happy_var_1
	)}

happyReduce_27 = happySpecReduce_2  7# happyReduction_27
happyReduction_27 happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_1 of { (HappyWrap25 happy_var_1) -> 
	case happyOut18 happy_x_2 of { (HappyWrap18 happy_var_2) -> 
	happyIn25
		 (E.Abs.CACons happy_var_1 happy_var_2
	)}}

happyReduce_28 = happySpecReduce_1  8# happyReduction_28
happyReduction_28 happy_x_1
	 =  case happyOut28 happy_x_1 of { (HappyWrap28 happy_var_1) -> 
	happyIn26
		 (E.Abs.SE happy_var_1
	)}

happyReduce_29 = happyReduce 7# 8# happyReduction_29
happyReduction_29 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { (HappyWrap28 happy_var_2) -> 
	case happyOut26 happy_x_4 of { (HappyWrap26 happy_var_4) -> 
	case happyOut26 happy_x_6 of { (HappyWrap26 happy_var_6) -> 
	happyIn26
		 (E.Abs.If happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_30 = happyReduce 5# 8# happyReduction_30
happyReduction_30 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_3 of { (HappyWrap28 happy_var_3) -> 
	case happyOut26 happy_x_5 of { (HappyWrap26 happy_var_5) -> 
	happyIn26
		 (E.Abs.While happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_31 = happySpecReduce_2  8# happyReduction_31
happyReduction_31 happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_2 of { (HappyWrap28 happy_var_2) -> 
	happyIn26
		 (E.Abs.Return happy_var_2
	)}

happyReduce_32 = happyReduce 4# 8# happyReduction_32
happyReduction_32 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut27 happy_x_3 of { (HappyWrap27 happy_var_3) -> 
	happyIn26
		 (E.Abs.Do happy_var_3
	) `HappyStk` happyRest}

happyReduce_33 = happySpecReduce_0  9# happyReduction_33
happyReduction_33  =  happyIn27
		 ([]
	)

happyReduce_34 = happySpecReduce_1  9# happyReduction_34
happyReduction_34 happy_x_1
	 =  case happyOut26 happy_x_1 of { (HappyWrap26 happy_var_1) -> 
	happyIn27
		 ((:[]) happy_var_1
	)}

happyReduce_35 = happySpecReduce_3  9# happyReduction_35
happyReduction_35 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut26 happy_x_1 of { (HappyWrap26 happy_var_1) -> 
	case happyOut27 happy_x_3 of { (HappyWrap27 happy_var_3) -> 
	happyIn27
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_36 = happySpecReduce_3  10# happyReduction_36
happyReduction_36 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_1 of { (HappyWrap31 happy_var_1) -> 
	case happyOut29 happy_x_3 of { (HappyWrap29 happy_var_3) -> 
	happyIn28
		 (E.Abs.Assign happy_var_1 happy_var_3
	)}}

happyReduce_37 = happySpecReduce_1  10# happyReduction_37
happyReduction_37 happy_x_1
	 =  case happyOut29 happy_x_1 of { (HappyWrap29 happy_var_1) -> 
	happyIn28
		 (happy_var_1
	)}

happyReduce_38 = happySpecReduce_3  11# happyReduction_38
happyReduction_38 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { (HappyWrap30 happy_var_1) -> 
	case happyOut21 happy_x_2 of { (HappyWrap21 happy_var_2) -> 
	case happyOut34 happy_x_3 of { (HappyWrap34 happy_var_3) -> 
	happyIn29
		 (E.Abs.Ops happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_39 = happySpecReduce_2  11# happyReduction_39
happyReduction_39 happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_1 of { (HappyWrap21 happy_var_1) -> 
	case happyOut29 happy_x_2 of { (HappyWrap29 happy_var_2) -> 
	happyIn29
		 (E.Abs.PrefixOp happy_var_1 happy_var_2
	)}}

happyReduce_40 = happySpecReduce_1  11# happyReduction_40
happyReduction_40 happy_x_1
	 =  case happyOut30 happy_x_1 of { (HappyWrap30 happy_var_1) -> 
	happyIn29
		 (happy_var_1
	)}

happyReduce_41 = happySpecReduce_2  12# happyReduction_41
happyReduction_41 happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { (HappyWrap30 happy_var_1) -> 
	case happyOut31 happy_x_2 of { (HappyWrap31 happy_var_2) -> 
	happyIn30
		 (E.Abs.App happy_var_1 happy_var_2
	)}}

happyReduce_42 = happySpecReduce_1  12# happyReduction_42
happyReduction_42 happy_x_1
	 =  case happyOut31 happy_x_1 of { (HappyWrap31 happy_var_1) -> 
	happyIn30
		 (happy_var_1
	)}

happyReduce_43 = happySpecReduce_1  13# happyReduction_43
happyReduction_43 happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	happyIn31
		 (E.Abs.Var happy_var_1
	)}

happyReduce_44 = happySpecReduce_1  13# happyReduction_44
happyReduction_44 happy_x_1
	 =  case happyOut20 happy_x_1 of { (HappyWrap20 happy_var_1) -> 
	happyIn31
		 (E.Abs.Con happy_var_1
	)}

happyReduce_45 = happySpecReduce_3  13# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut31 happy_x_1 of { (HappyWrap31 happy_var_1) -> 
	case happyOut18 happy_x_3 of { (HappyWrap18 happy_var_3) -> 
	happyIn31
		 (E.Abs.Dot happy_var_1 happy_var_3
	)}}

happyReduce_46 = happySpecReduce_1  13# happyReduction_46
happyReduction_46 happy_x_1
	 =  case happyOut19 happy_x_1 of { (HappyWrap19 happy_var_1) -> 
	happyIn31
		 (E.Abs.Int happy_var_1
	)}

happyReduce_47 = happySpecReduce_2  13# happyReduction_47
happyReduction_47 happy_x_2
	happy_x_1
	 =  happyIn31
		 (E.Abs.EmptyTup
	)

happyReduce_48 = happyReduce 5# 13# happyReduction_48
happyReduction_48 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut28 happy_x_2 of { (HappyWrap28 happy_var_2) -> 
	case happyOut32 happy_x_4 of { (HappyWrap32 happy_var_4) -> 
	happyIn31
		 (E.Abs.Tup happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_49 = happySpecReduce_2  13# happyReduction_49
happyReduction_49 happy_x_2
	happy_x_1
	 =  happyIn31
		 (E.Abs.EmptyStruct
	)

happyReduce_50 = happySpecReduce_3  13# happyReduction_50
happyReduction_50 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_2 of { (HappyWrap33 happy_var_2) -> 
	happyIn31
		 (E.Abs.EStruct happy_var_2
	)}

happyReduce_51 = happySpecReduce_1  13# happyReduction_51
happyReduction_51 happy_x_1
	 =  happyIn31
		 (E.Abs.Wild
	)

happyReduce_52 = happySpecReduce_3  13# happyReduction_52
happyReduction_52 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_2 of { (HappyWrap28 happy_var_2) -> 
	happyIn31
		 (happy_var_2
	)}

happyReduce_53 = happySpecReduce_0  14# happyReduction_53
happyReduction_53  =  happyIn32
		 ([]
	)

happyReduce_54 = happySpecReduce_1  14# happyReduction_54
happyReduction_54 happy_x_1
	 =  case happyOut28 happy_x_1 of { (HappyWrap28 happy_var_1) -> 
	happyIn32
		 ((:[]) happy_var_1
	)}

happyReduce_55 = happySpecReduce_3  14# happyReduction_55
happyReduction_55 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut28 happy_x_1 of { (HappyWrap28 happy_var_1) -> 
	case happyOut32 happy_x_3 of { (HappyWrap32 happy_var_3) -> 
	happyIn32
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_56 = happySpecReduce_1  15# happyReduction_56
happyReduction_56 happy_x_1
	 =  case happyOut35 happy_x_1 of { (HappyWrap35 happy_var_1) -> 
	happyIn33
		 ((:[]) happy_var_1
	)}

happyReduce_57 = happySpecReduce_3  15# happyReduction_57
happyReduction_57 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut35 happy_x_1 of { (HappyWrap35 happy_var_1) -> 
	case happyOut33 happy_x_3 of { (HappyWrap33 happy_var_3) -> 
	happyIn33
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_58 = happySpecReduce_1  16# happyReduction_58
happyReduction_58 happy_x_1
	 =  case happyOut30 happy_x_1 of { (HappyWrap30 happy_var_1) -> 
	happyIn34
		 (E.Abs.OSNil happy_var_1
	)}

happyReduce_59 = happySpecReduce_3  16# happyReduction_59
happyReduction_59 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut30 happy_x_1 of { (HappyWrap30 happy_var_1) -> 
	case happyOut21 happy_x_2 of { (HappyWrap21 happy_var_2) -> 
	case happyOut34 happy_x_3 of { (HappyWrap34 happy_var_3) -> 
	happyIn34
		 (E.Abs.OSCons happy_var_1 happy_var_2 happy_var_3
	)}}}

happyReduce_60 = happySpecReduce_3  17# happyReduction_60
happyReduction_60 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_2 of { (HappyWrap36 happy_var_2) -> 
	case happyOut35 happy_x_3 of { (HappyWrap35 happy_var_3) -> 
	happyIn35
		 (E.Abs.AnnotPad happy_var_2 happy_var_3
	)}}

happyReduce_61 = happySpecReduce_3  17# happyReduction_61
happyReduction_61 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_2 of { (HappyWrap36 happy_var_2) -> 
	case happyOut35 happy_x_3 of { (HappyWrap35 happy_var_3) -> 
	happyIn35
		 (E.Abs.AnnotAlign happy_var_2 happy_var_3
	)}}

happyReduce_62 = happySpecReduce_3  17# happyReduction_62
happyReduction_62 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { (HappyWrap18 happy_var_1) -> 
	case happyOut28 happy_x_3 of { (HappyWrap28 happy_var_3) -> 
	happyIn35
		 (E.Abs.Named happy_var_1 happy_var_3
	)}}

happyReduce_63 = happySpecReduce_1  17# happyReduction_63
happyReduction_63 happy_x_1
	 =  case happyOut28 happy_x_1 of { (HappyWrap28 happy_var_1) -> 
	happyIn35
		 (E.Abs.Anon happy_var_1
	)}

happyReduce_64 = happySpecReduce_1  18# happyReduction_64
happyReduction_64 happy_x_1
	 =  happyIn36
		 (E.Abs.Bit
	)

happyReduce_65 = happySpecReduce_1  18# happyReduction_65
happyReduction_65 happy_x_1
	 =  happyIn36
		 (E.Abs.Byte
	)

happyReduce_66 = happySpecReduce_1  18# happyReduction_66
happyReduction_66 happy_x_1
	 =  happyIn36
		 (E.Abs.Word
	)

happyNewToken action sts stk [] =
	happyDoAction 30# notHappyAtAll action sts stk []

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
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TV happy_dollar_dollar) -> cont 26#;
	PT _ (TI happy_dollar_dollar) -> cont 27#;
	PT _ (T_UIdent happy_dollar_dollar) -> cont 28#;
	PT _ (T_Infix happy_dollar_dollar) -> cont 29#;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 30# tk tks = happyError' (tks, explist)
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
pM tks = happySomeParser where
 happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (let {(HappyWrap22 x') = happyOut22 x} in x'))

pListD tks = happySomeParser where
 happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (let {(HappyWrap23 x') = happyOut23 x} in x'))

pD tks = happySomeParser where
 happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (let {(HappyWrap24 x') = happyOut24 x} in x'))

pConArgs tks = happySomeParser where
 happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (let {(HappyWrap25 x') = happyOut25 x} in x'))

pS tks = happySomeParser where
 happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (let {(HappyWrap26 x') = happyOut26 x} in x'))

pListS tks = happySomeParser where
 happySomeParser = happyThen (happyParse 5# tks) (\x -> happyReturn (let {(HappyWrap27 x') = happyOut27 x} in x'))

pE tks = happySomeParser where
 happySomeParser = happyThen (happyParse 6# tks) (\x -> happyReturn (let {(HappyWrap28 x') = happyOut28 x} in x'))

pE1 tks = happySomeParser where
 happySomeParser = happyThen (happyParse 7# tks) (\x -> happyReturn (let {(HappyWrap29 x') = happyOut29 x} in x'))

pE2 tks = happySomeParser where
 happySomeParser = happyThen (happyParse 8# tks) (\x -> happyReturn (let {(HappyWrap30 x') = happyOut30 x} in x'))

pE3 tks = happySomeParser where
 happySomeParser = happyThen (happyParse 9# tks) (\x -> happyReturn (let {(HappyWrap31 x') = happyOut31 x} in x'))

pListE tks = happySomeParser where
 happySomeParser = happyThen (happyParse 10# tks) (\x -> happyReturn (let {(HappyWrap32 x') = happyOut32 x} in x'))

pListField tks = happySomeParser where
 happySomeParser = happyThen (happyParse 11# tks) (\x -> happyReturn (let {(HappyWrap33 x') = happyOut33 x} in x'))

pOS tks = happySomeParser where
 happySomeParser = happyThen (happyParse 12# tks) (\x -> happyReturn (let {(HappyWrap34 x') = happyOut34 x} in x'))

pField tks = happySomeParser where
 happySomeParser = happyThen (happyParse 13# tks) (\x -> happyReturn (let {(HappyWrap35 x') = happyOut35 x} in x'))

pPadInfo tks = happySomeParser where
 happySomeParser = happyThen (happyParse 14# tks) (\x -> happyReturn (let {(HappyWrap36 x') = happyOut36 x} in x'))

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
