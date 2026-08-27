{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Float.Decimal

-- Once.Arith.Backend.XInstr.Syntax.XReg
d_XReg_10 = ()
data T_XReg_10 = C_XR0_12 | C_XR1_14
-- Once.Arith.Backend.XInstr.Syntax.XScratch
d_XScratch_16 = ()
newtype T_XScratch_16 = C_mk'45'scratch_22 Integer
-- Once.Arith.Backend.XInstr.Syntax.XScratch.slot
d_slot_20 :: T_XScratch_16 -> Integer
d_slot_20 v0
  = case coe v0 of
      C_mk'45'scratch_22 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.XInstr.Syntax.XInstr
d_XInstr_24 = ()
data T_XInstr_24
  = C_Xmov'45'imm_26 T_XReg_10 Integer |
    C_Xmov'45'rr_28 T_XReg_10 T_XReg_10 |
    C_Xmov'45'r'45'm_30 T_XScratch_16 T_XReg_10 |
    C_Xmov'45'm'45'r_32 T_XReg_10 T_XScratch_16 |
    C_Xmov'45'arg_34 T_XReg_10
                     [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] |
    C_Xadd'45'rr_36 T_XReg_10 T_XReg_10 |
    C_Xsub'45'rr_38 T_XReg_10 T_XReg_10 |
    C_Ximul'45'rr_40 T_XReg_10 T_XReg_10 | C_Xneg'45'r_42 T_XReg_10 |
    C_Xdiv'45'rrr_44 T_XReg_10 T_XReg_10 T_XReg_10 |
    C_Xrem'45'rrr_46 T_XReg_10 T_XReg_10 T_XReg_10 |
    C_Xdiv'45'safe'45'rrr_48 T_XReg_10 T_XReg_10 T_XReg_10 |
    C_Xrem'45'safe'45'rrr_50 T_XReg_10 T_XReg_10 T_XReg_10 |
    C_Xshl'45'rri_52 T_XReg_10 T_XReg_10 Integer |
    C_Xsdiv'45'pow2'45'rri_54 T_XReg_10 T_XReg_10 Integer |
    C_Xfadd'45'rr_56 T_XReg_10 T_XReg_10 |
    C_Xfsub'45'rr_58 T_XReg_10 T_XReg_10 |
    C_Xfmul'45'rr_60 T_XReg_10 T_XReg_10 |
    C_Xfsubr'45'rr_62 T_XReg_10 T_XReg_10 | C_Xfneg'45'r_64 T_XReg_10 |
    C_Xi2f'45'r_66 T_XReg_10 T_XReg_10 |
    C_Xmov'45'fimm_68 T_XReg_10
                      MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 |
    C_Xmov'45'farg_70 T_XReg_10
                      [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] |
    C_Xmov'45'out_72 T_XReg_10
-- Once.Arith.Backend.XInstr.Syntax.XProgram
d_XProgram_74 :: ()
d_XProgram_74 = erased
