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

module MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Target.X86-64.PhysReg.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_rax_10 | C_rbx_12 | C_rcx_14 | C_rdx_16 | C_rsi_18 | C_rdi_20 |
    C_rbp_22 | C_rsp_24 | C_r8_26 | C_r9_28 | C_r10_30 | C_r11_32 |
    C_r12_34 | C_r13_36 | C_r14_38 | C_r15_40
-- Once.Target.X86-64.PhysReg.showReg
d_showReg_42 ::
  T_Reg_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_42 v0
  = case coe v0 of
      C_rax_10 -> coe ("%rax" :: Data.Text.Text)
      C_rbx_12 -> coe ("%rbx" :: Data.Text.Text)
      C_rcx_14 -> coe ("%rcx" :: Data.Text.Text)
      C_rdx_16 -> coe ("%rdx" :: Data.Text.Text)
      C_rsi_18 -> coe ("%rsi" :: Data.Text.Text)
      C_rdi_20 -> coe ("%rdi" :: Data.Text.Text)
      C_rbp_22 -> coe ("%rbp" :: Data.Text.Text)
      C_rsp_24 -> coe ("%rsp" :: Data.Text.Text)
      C_r8_26 -> coe ("%r8" :: Data.Text.Text)
      C_r9_28 -> coe ("%r9" :: Data.Text.Text)
      C_r10_30 -> coe ("%r10" :: Data.Text.Text)
      C_r11_32 -> coe ("%r11" :: Data.Text.Text)
      C_r12_34 -> coe ("%r12" :: Data.Text.Text)
      C_r13_36 -> coe ("%r13" :: Data.Text.Text)
      C_r14_38 -> coe ("%r14" :: Data.Text.Text)
      C_r15_40 -> coe ("%r15" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.X86-64.PhysReg.RegClass
d_RegClass_44 = ()
data T_RegClass_44 = C_io_46 | C_ccc_48 | C_arith_50 | C_free_52
-- Once.Target.X86-64.PhysReg.owner
d_owner_54 :: T_Reg_8 -> T_RegClass_44
d_owner_54 v0
  = case coe v0 of
      C_rax_10 -> coe C_io_46
      C_rbx_12 -> coe C_ccc_48
      C_rcx_14 -> coe C_ccc_48
      C_rdx_16 -> coe C_free_52
      C_rsi_18 -> coe C_ccc_48
      C_rdi_20 -> coe C_io_46
      C_rbp_22 -> coe C_ccc_48
      C_rsp_24 -> coe C_ccc_48
      C_r8_26 -> coe C_arith_50
      C_r9_28 -> coe C_arith_50
      C_r10_30 -> coe C_arith_50
      C_r11_32 -> coe C_arith_50
      C_r12_34 -> coe C_ccc_48
      C_r13_36 -> coe C_free_52
      C_r14_38 -> coe C_free_52
      C_r15_40 -> coe C_ccc_48
      _ -> MAlonzo.RTE.mazUnreachableError
