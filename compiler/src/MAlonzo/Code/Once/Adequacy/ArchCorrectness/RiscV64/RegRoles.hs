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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.RiscV64.RegRoles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles.riscv64-reg-of
d_riscv64'45'reg'45'of_10 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_riscv64'45'reg'45'of_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'sp_12
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'clos_14
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'heap_16
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'out_18
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'in1_20
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'in2_22
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a1_20
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'scratch_24
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s3_38
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_role'45'count_26
        -> coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s4_40
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles.riscv64-roles
d_riscv64'45'roles_12 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30
d_riscv64'45'roles_12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.C_constructor_54
      (coe d_riscv64'45'reg'45'of_10)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.clos-reg
d_clos'45'reg_16 ::
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_clos'45'reg_16
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_clos'45'reg_40
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.count-reg
d_count'45'reg_18 ::
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_count'45'reg_18
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_count'45'reg_52
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.heap-reg
d_heap'45'reg_20 ::
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_heap'45'reg_20
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_heap'45'reg_42
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.in1-reg
d_in1'45'reg_22 :: MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_in1'45'reg_22
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_46
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.in2-reg
d_in2'45'reg_24 :: MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_in2'45'reg_24
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in2'45'reg_48
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.out-reg
d_out'45'reg_26 :: MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_out'45'reg_26
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_44
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.reg-of
d_reg'45'of_28 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_reg'45'of_28 = coe d_riscv64'45'reg'45'of_10
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.scratch-reg
d_scratch'45'reg_30 ::
  MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_scratch'45'reg_30
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_50
      (coe d_riscv64'45'roles_12)
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles._.sp-reg
d_sp'45'reg_32 :: MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8
d_sp'45'reg_32
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
      (coe d_riscv64'45'roles_12)
