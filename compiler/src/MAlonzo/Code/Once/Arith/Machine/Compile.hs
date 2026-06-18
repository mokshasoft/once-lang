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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem

-- Once.Arith.Machine.Compile._.run-abstract
d_run'45'abstract_10 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_10
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer))
-- Once.Arith.Machine.Compile._.step
d_step_12 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_12
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64
      (coe (64 :: Integer))
-- Once.Arith.Machine.Compile._.eval-arith-W
d_eval'45'arith'45'W_16 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_16
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_28
      (coe (64 :: Integer))
-- Once.Arith.Machine.Compile.n-regs
d_n'45'regs_18 :: Integer
d_n'45'regs_18 = coe (2 :: Integer)
-- Once.Arith.Machine.Compile.required-scratch
d_required'45'scratch_22 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
d_required'45'scratch_22 ~v0 v1 = du_required'45'scratch_22 v1
du_required'45'scratch_22 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
du_required'45'scratch_22 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_22 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_22 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_22 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_22 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_22 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_22 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24 v1
        -> coe du_required'45'scratch_22 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-go
d_compile'45'go_40 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'go_40 ~v0 v1 v2 = du_compile'45'go_40 v1 v2
du_compile'45'go_40 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'go_40 v0 v1
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
             (coe du_compile'45'go_40 (coe v0) (coe v2))
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
                      du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v0))
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
             (coe du_compile'45'go_40 (coe v0) (coe v2))
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
                      du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v0))
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
             (coe du_compile'45'go_40 (coe v0) (coe v2))
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
                      du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v0))
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
             (coe du_compile'45'go_40 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_20
                   (coe (0 :: Integer)) (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-abs
d_compile'45'abs_74 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'abs_74 ~v0 v1 = du_compile'45'abs_74 v1
du_compile'45'abs_74 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
du_compile'45'abs_74 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe du_compile'45'go_40 (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_26
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Arith.Machine.Compile.CompileGoInv
d_CompileGoInv_86 a0 a1 a2 a3 = ()
data T_CompileGoInv_86 = C_constructor_116
-- Once.Arith.Machine.Compile.CompileGoInv.reg0
d_reg0_106 ::
  T_CompileGoInv_86 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg0_106 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.scratch≤
d_scratch'8804'_110 ::
  T_CompileGoInv_86 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'8804'_110 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.input-eq
d_input'45'eq_112 ::
  T_CompileGoInv_86 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'eq_112 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.output-eq
d_output'45'eq_114 ::
  T_CompileGoInv_86 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'eq_114 = erased
-- Once.Arith.Machine.Compile.run-abstract-app
d_run'45'abstract'45'app_126 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'abstract'45'app_126 = erased
-- Once.Arith.Machine.Compile.eval-arith-W-ainput
d_eval'45'arith'45'W'45'ainput_146 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'ainput_146 = erased
-- Once.Arith.Machine.Compile.compile-go-correct-ainput
d_compile'45'go'45'correct'45'ainput_178 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_compile'45'go'45'correct'45'ainput_178 = erased
-- Once.Arith.Machine.Compile.d≢i
d_d'8802'i_196 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8802'i_196 = erased
-- Once.Arith.Machine.Compile.<-suc
d_'60''45'suc_206 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'suc_206 ~v0 ~v1 v2 = du_'60''45'suc_206 v2
du_'60''45'suc_206 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'suc_206 v0 = coe v0
-- Once.Arith.Machine.Compile.compile-go-correct
d_compile'45'go'45'correct_218 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_compile'45'go'45'correct_218 = erased
-- Once.Arith.Machine.Compile.aneg-correct
d_aneg'45'correct_228 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_aneg'45'correct_228 = erased
-- Once.Arith.Machine.Compile._.ih
d_ih_242 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih_242 = erased
-- Once.Arith.Machine.Compile._.bridge
d_bridge_244 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_244 = erased
-- Once.Arith.Machine.Compile.aadd-correct
d_aadd'45'correct_264 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_aadd'45'correct_264 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_280 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'a_280 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_282 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_282 v0 v1 v2 ~v3 v4 = du_s1_282 v0 v1 v2 v4
du_s1_282 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_282 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe du_compile'45'go_40 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_284 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_284 v0 v1 v2 ~v3 v4 = du_s2_284 v0 v1 v2 v4
du_s2_284 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_284 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_282 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_286 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'b_286 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_288 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_288 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe
         du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_284 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_290 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_290 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_288 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_292 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_292 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_290 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_294 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_294 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_296 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_296 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_298 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_298 = erased
-- Once.Arith.Machine.Compile.asub-correct
d_asub'45'correct_320 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_asub'45'correct_320 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_336 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'a_336 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_338 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_338 v0 v1 v2 ~v3 v4 = du_s1_338 v0 v1 v2 v4
du_s1_338 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_338 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe du_compile'45'go_40 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_340 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_340 v0 v1 v2 ~v3 v4 = du_s2_340 v0 v1 v2 v4
du_s2_340 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_340 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_338 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_342 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'b_342 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_344 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_344 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe
         du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_340 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_346 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_346 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_344 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_348 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_348 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_350 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_350 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_352 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_352 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_354 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_354 = erased
-- Once.Arith.Machine.Compile.amul-correct
d_amul'45'correct_376 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_amul'45'correct_376 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_392 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'a_392 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_394 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_394 v0 v1 v2 ~v3 v4 = du_s1_394 v0 v1 v2 v4
du_s1_394 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_394 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe du_compile'45'go_40 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_396 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_396 v0 v1 v2 ~v3 v4 = du_s2_396 v0 v1 v2 v4
du_s2_396 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_396 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_394 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_398 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_86
d_ih'45'b_398 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_400 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_128
      (coe (64 :: Integer)) (coe v0)
      (coe
         du_compile'45'go_40 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_396 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_402 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_400 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_404 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_404 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_64 (64 :: Integer)
      v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_406 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_406 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_408 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_408 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_410 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_410 = erased
-- Once.Arith.Machine.Compile.abs-validity-from-inv
d_abs'45'validity'45'from'45'inv_476 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'from'45'inv_476 = erased
-- Once.Arith.Machine.Compile.abs-validity-alit
d_abs'45'validity'45'alit_490 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'alit_490 = erased
-- Once.Arith.Machine.Compile.abs-validity-ainput
d_abs'45'validity'45'ainput_502 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'ainput_502 = erased
-- Once.Arith.Machine.Compile.abs-validity-aadd
d_abs'45'validity'45'aadd_516 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'aadd_516 = erased
-- Once.Arith.Machine.Compile.abs-validity-asub
d_abs'45'validity'45'asub_532 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'asub_532 = erased
-- Once.Arith.Machine.Compile.abs-validity-amul
d_abs'45'validity'45'amul_548 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'amul_548 = erased
-- Once.Arith.Machine.Compile.abs-validity-aneg
d_abs'45'validity'45'aneg_562 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'aneg_562 = erased
-- Once.Arith.Machine.Compile.abs-validity
d_abs'45'validity_574 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_574 = erased
