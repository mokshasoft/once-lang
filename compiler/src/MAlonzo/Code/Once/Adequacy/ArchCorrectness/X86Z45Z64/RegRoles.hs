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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles.x86-64-reg-of
d_x86'45'64'45'reg'45'of_10 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_x86'45'64'45'reg'45'of_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'sp_12
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'clos_14
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r12_34
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'heap_16
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r15_40
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'out_18
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rax_10
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'in1_20
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rdi_20
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'scratch_22
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rbx_12
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'count_24
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_r14_38
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles.x86-64-roles
d_x86'45'64'45'roles_12 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28
d_x86'45'64'45'roles_12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_constructor_50
      (coe d_x86'45'64'45'reg'45'of_10)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.clos-reg
d_clos'45'reg_16 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_clos'45'reg_16
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_clos'45'reg_38
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.count-reg
d_count'45'reg_18 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_count'45'reg_18
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_count'45'reg_48
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.heap-reg
d_heap'45'reg_20 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_heap'45'reg_20
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_heap'45'reg_40
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.in1-reg
d_in1'45'reg_22 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_in1'45'reg_22
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_44
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.out-reg
d_out'45'reg_24 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_out'45'reg_24
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_42
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.reg-of
d_reg'45'of_26 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_reg'45'of_26 = coe d_x86'45'64'45'reg'45'of_10
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.scratch-reg
d_scratch'45'reg_28 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_scratch'45'reg_28
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_46
      (coe d_x86'45'64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles._.sp-reg
d_sp'45'reg_30 ::
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_sp'45'reg_30
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
      (coe d_x86'45'64'45'roles_12)
