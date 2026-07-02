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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Target.RegConvention

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
-- Once.Target.X86-64.PhysReg.owner
d_owner_44 ::
  T_Reg_8 -> MAlonzo.Code.Once.Target.RegConvention.T_RegClass_6
d_owner_44 v0
  = case coe v0 of
      C_rax_10 -> coe MAlonzo.Code.Once.Target.RegConvention.C_io_8
      C_rbx_12 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_rcx_14 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_rdx_16 -> coe MAlonzo.Code.Once.Target.RegConvention.C_free_14
      C_rsi_18 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_rdi_20 -> coe MAlonzo.Code.Once.Target.RegConvention.C_io_8
      C_rbp_22 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_rsp_24 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_r8_26 -> coe MAlonzo.Code.Once.Target.RegConvention.C_arith_12
      C_r9_28 -> coe MAlonzo.Code.Once.Target.RegConvention.C_arith_12
      C_r10_30 -> coe MAlonzo.Code.Once.Target.RegConvention.C_arith_12
      C_r11_32 -> coe MAlonzo.Code.Once.Target.RegConvention.C_arith_12
      C_r12_34 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_r13_36 -> coe MAlonzo.Code.Once.Target.RegConvention.C_free_14
      C_r14_38 -> coe MAlonzo.Code.Once.Target.RegConvention.C_free_14
      C_r15_40 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.X86-64.PhysReg.arith-budget
d_arith'45'budget_46 :: [T_Reg_8]
d_arith'45'budget_46
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_r8_26)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_r9_28)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_r10_30)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_r11_32)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.Target.X86-64.PhysReg.convention
d_convention_48 ::
  MAlonzo.Code.Once.Target.RegConvention.T_RegConvention_16
d_convention_48
  = coe
      MAlonzo.Code.Once.Target.RegConvention.C_constructor_42
      d_showReg_42 d_owner_44 d_arith'45'budget_46
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
