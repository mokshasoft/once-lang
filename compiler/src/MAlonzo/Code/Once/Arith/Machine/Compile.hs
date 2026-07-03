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
import qualified MAlonzo.Code.Agda.Builtin.Bool
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
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_12 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_12 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_12 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_12 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v1
        -> coe du_required'45'scratch_12 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.safe-lit?
d_safe'45'lit'63'_36 :: Integer -> Bool
d_safe'45'lit'63'_36 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      -1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.Arith.Machine.Compile.safe-divisor?
d_safe'45'divisor'63'_40 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
d_safe'45'divisor'63'_40 ~v0 v1 = du_safe'45'divisor'63'_40 v1
du_safe'45'divisor'63'_40 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
du_safe'45'divisor'63'_40 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v2
           -> coe d_safe'45'lit'63'_36 (coe v2)
         _ -> coe v1)
-- Once.Arith.Machine.Compile.div-instr
d_div'45'instr_44 ::
  Bool -> MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_div'45'instr_44 v0
  = if coe v0
      then coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_24
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
      else coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.Machine.Compile.rem-instr
d_rem'45'instr_46 ::
  Bool -> MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_rem'45'instr_46 v0
  = if coe v0
      then coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_26
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
      else coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.Machine.Compile.div-op
d_div'45'op_50 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_div'45'op_50 ~v0 v1 = du_div'45'op_50 v1
du_div'45'op_50 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
du_div'45'op_50 v0
  = coe d_div'45'instr_44 (coe du_safe'45'divisor'63'_40 (coe v0))
-- Once.Arith.Machine.Compile.rem-op
d_rem'45'op_54 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_rem'45'op_54 ~v0 v1 = du_rem'45'op_54 v1
du_rem'45'op_54 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
du_rem'45'op_54 v0
  = coe d_rem'45'instr_46 (coe du_safe'45'divisor'63'_40 (coe v0))
-- Once.Arith.Machine.Compile.compile-go
d_compile'45'go_62 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'go_62 ~v0 v1 v2 = du_compile'45'go_62 v1 v2
du_compile'45'go_62 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'go_62 v0 v1
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
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_30
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_62 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_32 (coe v0)
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
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_30
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_62 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_32 (coe v0)
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
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_30
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_62 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_32 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
                            (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_30
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_62 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_32 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe du_div'45'op_50 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_30
                      (coe (0 :: Integer)) (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      du_compile'45'go_62 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_32 (coe v0)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe du_rem'45'op_54 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_compile'45'go_62 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_28
                   (coe (0 :: Integer)) (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-abs
d_compile'45'abs_108 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'abs_108 ~v0 v1 = du_compile'45'abs_108 v1
du_compile'45'abs_108 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'abs_108 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe du_compile'45'go_62 (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_34
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Arith.Machine.Compile.fold-div
d_fold'45'div_114 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_fold'45'div_114 ~v0 v1 v2 = du_fold'45'div_114 v1 v2
du_fold'45'div_114 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_fold'45'div_114 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 (coe v0) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
           -> case coe v3 of
                0 -> coe
                       MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 (coe (-1 :: Integer))
                _ | coe geqInt (coe v3) (coe (0 :: Integer)) -> coe v2
                -1 -> coe MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 (coe v0)
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Compile.fold-mod
d_fold'45'mod_118 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_fold'45'mod_118 ~v0 v1 v2 = du_fold'45'mod_118 v1 v2
du_fold'45'mod_118 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_fold'45'mod_118 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 (coe v0) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
           -> case coe v3 of
                0 -> coe v0
                _ | coe geqInt (coe v3) (coe (0 :: Integer)) -> coe v2
                -1
                  -> coe
                       MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 (coe (0 :: Integer))
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Compile.normalize
d_normalize_138 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_normalize_138 ~v0 v1 = du_normalize_138 v1
du_normalize_138 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_normalize_138 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1 -> coe v0
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1 -> coe v0
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18
             (coe du_normalize_138 (coe v1)) (coe du_normalize_138 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20
             (coe du_normalize_138 (coe v1)) (coe du_normalize_138 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22
             (coe du_normalize_138 (coe v1)) (coe du_normalize_138 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v1 v2
        -> coe
             du_fold'45'div_114 (coe du_normalize_138 (coe v1))
             (coe du_normalize_138 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v1 v2
        -> coe
             du_fold'45'mod_118 (coe du_normalize_138 (coe v1))
             (coe du_normalize_138 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28
             (coe du_normalize_138 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
