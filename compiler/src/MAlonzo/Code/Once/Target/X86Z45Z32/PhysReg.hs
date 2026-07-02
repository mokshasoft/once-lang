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

module MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Target.RegConvention

-- Once.Target.X86-32.PhysReg.Reg
d_Reg_8 = ()
data T_Reg_8
  = C_eax_10 | C_ebx_12 | C_ecx_14 | C_edx_16 | C_esi_18 | C_edi_20 |
    C_ebp_22 | C_esp_24
-- Once.Target.X86-32.PhysReg.showReg
d_showReg_26 ::
  T_Reg_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showReg_26 v0
  = case coe v0 of
      C_eax_10 -> coe ("%eax" :: Data.Text.Text)
      C_ebx_12 -> coe ("%ebx" :: Data.Text.Text)
      C_ecx_14 -> coe ("%ecx" :: Data.Text.Text)
      C_edx_16 -> coe ("%edx" :: Data.Text.Text)
      C_esi_18 -> coe ("%esi" :: Data.Text.Text)
      C_edi_20 -> coe ("%edi" :: Data.Text.Text)
      C_ebp_22 -> coe ("%ebp" :: Data.Text.Text)
      C_esp_24 -> coe ("%esp" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.X86-32.PhysReg.owner
d_owner_28 ::
  T_Reg_8 -> MAlonzo.Code.Once.Target.RegConvention.T_RegClass_6
d_owner_28 v0
  = case coe v0 of
      C_eax_10 -> coe MAlonzo.Code.Once.Target.RegConvention.C_io_8
      C_ebx_12 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_ecx_14 -> coe MAlonzo.Code.Once.Target.RegConvention.C_io_8
      C_edx_16 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_esi_18 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_edi_20 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_ebp_22 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      C_esp_24 -> coe MAlonzo.Code.Once.Target.RegConvention.C_ccc_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.X86-32.PhysReg.arith-budget
d_arith'45'budget_30 :: [T_Reg_8]
d_arith'45'budget_30
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Target.X86-32.PhysReg.convention
d_convention_32 ::
  MAlonzo.Code.Once.Target.RegConvention.T_RegConvention_16
d_convention_32
  = coe
      MAlonzo.Code.Once.Target.RegConvention.C_constructor_42
      d_showReg_26 d_owner_28 d_arith'45'budget_30
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
