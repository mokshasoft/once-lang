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

-- Once.Arith.Machine.Compile.n-regs
d_n'45'regs_8 :: Integer
d_n'45'regs_8 = coe (2 :: Integer)
-- Once.Arith.Machine.Compile.required-scratch
d_required'45'scratch_12 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
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
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
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
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
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
-- Once.Arith.Machine.Compile.CompileGoInv
d_CompileGoInv_76 a0 a1 a2 a3 = ()
data T_CompileGoInv_76 = C_constructor_106
-- Once.Arith.Machine.Compile.CompileGoInv.reg0
d_reg0_96 ::
  T_CompileGoInv_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg0_96 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.scratch≤
d_scratch'8804'_100 ::
  T_CompileGoInv_76 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'8804'_100 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.input-eq
d_input'45'eq_102 ::
  T_CompileGoInv_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'eq_102 = erased
-- Once.Arith.Machine.Compile.CompileGoInv.output-eq
d_output'45'eq_104 ::
  T_CompileGoInv_76 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'eq_104 = erased
-- Once.Arith.Machine.Compile.run-abstract-app
d_run'45'abstract'45'app_116 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'abstract'45'app_116 = erased
-- Once.Arith.Machine.Compile.eval-arith-W-ainput
d_eval'45'arith'45'W'45'ainput_136 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'ainput_136 = erased
-- Once.Arith.Machine.Compile.compile-go-correct-ainput
d_compile'45'go'45'correct'45'ainput_168 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_compile'45'go'45'correct'45'ainput_168 = erased
-- Once.Arith.Machine.Compile.d≢i
d_d'8802'i_186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8802'i_186 = erased
-- Once.Arith.Machine.Compile.<-suc
d_'60''45'suc_196 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'suc_196 ~v0 ~v1 v2 = du_'60''45'suc_196 v2
du_'60''45'suc_196 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'suc_196 v0 = coe v0
-- Once.Arith.Machine.Compile.compile-go-correct
d_compile'45'go'45'correct_208 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_compile'45'go'45'correct_208 = erased
-- Once.Arith.Machine.Compile.aneg-correct
d_aneg'45'correct_218 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_aneg'45'correct_218 = erased
-- Once.Arith.Machine.Compile._.ih
d_ih_232 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih_232 = erased
-- Once.Arith.Machine.Compile._.bridge
d_bridge_234 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_234 = erased
-- Once.Arith.Machine.Compile.aadd-correct
d_aadd'45'correct_254 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_aadd'45'correct_254 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_270 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'a_270 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_272 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s1_272 v0 v1 v2 ~v3 v4 = du_s1_272 v0 v1 v2 v4
du_s1_272 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s1_272 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0) (coe du_compile'45'go_30 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_274 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s2_274 v0 v1 v2 ~v3 v4 = du_s2_274 v0 v1 v2 v4
du_s2_274 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s2_274 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_272 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_276 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'b_276 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_278 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s3_278 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0)
      (coe
         du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_274 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_280 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s4_280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_278 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_282 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s5_282 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_280 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_284 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_284 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_286 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_286 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_288 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_288 = erased
-- Once.Arith.Machine.Compile.asub-correct
d_asub'45'correct_310 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_asub'45'correct_310 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_326 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'a_326 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_328 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s1_328 v0 v1 v2 ~v3 v4 = du_s1_328 v0 v1 v2 v4
du_s1_328 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s1_328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0) (coe du_compile'45'go_30 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_330 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s2_330 v0 v1 v2 ~v3 v4 = du_s2_330 v0 v1 v2 v4
du_s2_330 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s2_330 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_328 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_332 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'b_332 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_334 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s3_334 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0)
      (coe
         du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_330 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_336 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s4_336 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_334 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_338 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s5_338 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_336 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_340 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_340 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_342 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_342 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_344 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_344 = erased
-- Once.Arith.Machine.Compile.amul-correct
d_amul'45'correct_366 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_amul'45'correct_366 = erased
-- Once.Arith.Machine.Compile._.ih-a
d_ih'45'a_382 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'a_382 = erased
-- Once.Arith.Machine.Compile._.s1
d_s1_384 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s1_384 v0 v1 v2 ~v3 v4 = du_s1_384 v0 v1 v2 v4
du_s1_384 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s1_384 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0) (coe du_compile'45'go_30 (coe v1) (coe v2)) (coe v3)
-- Once.Arith.Machine.Compile._.s2
d_s2_386 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s2_386 v0 v1 v2 ~v3 v4 = du_s2_386 v0 v1 v2 v4
du_s2_386 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
du_s2_386 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_22
         (coe (0 :: Integer)) (coe v1))
      (coe du_s1_384 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Arith.Machine.Compile._.ih-b
d_ih'45'b_388 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  T_CompileGoInv_76
d_ih'45'b_388 = erased
-- Once.Arith.Machine.Compile._.s3
d_s3_390 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s3_390 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_112
      (coe v0)
      (coe
         du_compile'45'go_30 (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v3))
      (coe du_s2_386 (coe v0) (coe v1) (coe v2) (coe v4))
-- Once.Arith.Machine.Compile._.s4
d_s4_392 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s4_392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_24 (coe v1)
         (coe (1 :: Integer)))
      (d_s3_390 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.s5
d_s5_394 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_s5_394 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_48 v0
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_392 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.Compile._.bridge
d_bridge_396 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_396 = erased
-- Once.Arith.Machine.Compile._.scratch-s3-d
d_scratch'45's3'45'd_398 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_398 = erased
-- Once.Arith.Machine.Compile._.regs-s3-0
d_regs'45's3'45'0_400 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_400 = erased
-- Once.Arith.Machine.Compile.abs-validity-from-inv
d_abs'45'validity'45'from'45'inv_466 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'from'45'inv_466 = erased
-- Once.Arith.Machine.Compile.abs-validity-alit
d_abs'45'validity'45'alit_480 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'alit_480 = erased
-- Once.Arith.Machine.Compile.abs-validity-ainput
d_abs'45'validity'45'ainput_492 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'ainput_492 = erased
-- Once.Arith.Machine.Compile.abs-validity-aadd
d_abs'45'validity'45'aadd_506 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'aadd_506 = erased
-- Once.Arith.Machine.Compile.abs-validity-asub
d_abs'45'validity'45'asub_522 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'asub_522 = erased
-- Once.Arith.Machine.Compile.abs-validity-amul
d_abs'45'validity'45'amul_538 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'amul_538 = erased
-- Once.Arith.Machine.Compile.abs-validity-aneg
d_abs'45'validity'45'aneg_552 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity'45'aneg_552 = erased
-- Once.Arith.Machine.Compile.abs-validity
d_abs'45'validity_564 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_564 = erased
