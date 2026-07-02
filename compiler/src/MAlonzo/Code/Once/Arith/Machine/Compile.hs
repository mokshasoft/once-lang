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

module MAlonzo.Code.Once.Arith.Machine.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape

-- Once.Arith.Machine.Compile.n-regs
d_n'45'regs_8 :: Integer
d_n'45'regs_8 = coe (2 :: Integer)
-- Once.Arith.Machine.Compile.required-scratch
d_required'45'scratch_12 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
d_required'45'scratch_12 ~v0 v1 = du_required'45'scratch_12 v1
du_required'45'scratch_12 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
du_required'45'scratch_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_12 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_12 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_12 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_12 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_12 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_12 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v1
        -> coe du_required'45'scratch_12 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-go
d_compile'45'go_30 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'go_30 ~v0 v1 v2 = du_compile'45'go_30 v1 v2
du_compile'45'go_30 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'go_30 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 (coe v2)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10
                (coe v2) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_30 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
                            (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_30 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
                            (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_30 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
                            (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_30 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_20
                   (coe (0 :: Integer)) (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-abs
d_compile'45'abs_64 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'abs_64 ~v0 v1 = du_compile'45'abs_64 v1
du_compile'45'abs_64 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'abs_64 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe du_compile'45'go_30 (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_26
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
