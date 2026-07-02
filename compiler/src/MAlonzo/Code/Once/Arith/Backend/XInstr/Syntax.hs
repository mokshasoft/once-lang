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

-- Once.Arith.Backend.XInstr.Syntax.XReg
d_XReg_10 = ()
data T_XReg_10 = C_XR0_12 | C_XR1_14 | C_XR2_16 | C_XR3_18
-- Once.Arith.Backend.XInstr.Syntax.XScratch
d_XScratch_20 = ()
newtype T_XScratch_20 = C_mk'45'scratch_26 Integer
-- Once.Arith.Backend.XInstr.Syntax.XScratch.slot
d_slot_24 :: T_XScratch_20 -> Integer
d_slot_24 v0
  = case coe v0 of
      C_mk'45'scratch_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.XInstr.Syntax.XInstr
d_XInstr_28 = ()
data T_XInstr_28
  = C_Xmov'45'imm_30 T_XReg_10 Integer |
    C_Xmov'45'rr_32 T_XReg_10 T_XReg_10 |
    C_Xmov'45'r'45'm_34 T_XScratch_20 T_XReg_10 |
    C_Xmov'45'm'45'r_36 T_XReg_10 T_XScratch_20 |
    C_Xmov'45'arg_38 T_XReg_10
                     [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] |
    C_Xadd'45'rr_40 T_XReg_10 T_XReg_10 |
    C_Xsub'45'rr_42 T_XReg_10 T_XReg_10 |
    C_Ximul'45'rr_44 T_XReg_10 T_XReg_10 | C_Xneg'45'r_46 T_XReg_10 |
    C_Xmov'45'out_48 T_XReg_10
-- Once.Arith.Backend.XInstr.Syntax.XProgram
d_XProgram_50 :: ()
d_XProgram_50 = erased
