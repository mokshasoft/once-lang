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

module MAlonzo.Code.Once.Arith.Backend.Correct where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Backend.Correct._.eval-arith-W
d_eval'45'arith'45'W_14 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_14 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
      (coe v0) (coe v1)
-- Once.Arith.Backend.Correct._._⊕_
d__'8853'__26 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d__'8853'__26 v0 ~v1 = du__'8853'__26 v0
du__'8853'__26 :: Integer -> Integer -> Integer -> Integer
du__'8853'__26 v0
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0)
-- Once.Arith.Backend.Correct._._⊖_
d__'8854'__28 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d__'8854'__28 v0 ~v1 = du__'8854'__28 v0
du__'8854'__28 :: Integer -> Integer -> Integer -> Integer
du__'8854'__28 v0
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0)
-- Once.Arith.Backend.Correct._._⊗_
d__'8855'__30 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d__'8855'__30 v0 ~v1 = du__'8855'__30 v0
du__'8855'__30 :: Integer -> Integer -> Integer -> Integer
du__'8855'__30 v0
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
-- Once.Arith.Backend.Correct._.norm
d_norm_38 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_norm_38 v0 ~v1 = du_norm_38 v0
du_norm_38 :: Integer -> Integer -> Integer
du_norm_38 v0 = coe MAlonzo.Code.Once.Word.d_norm_16 (coe v0)
-- Once.Arith.Backend.Correct._.⊝_
d_'8861'__46 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_'8861'__46 v0 ~v1 = du_'8861'__46 v0
du_'8861'__46 :: Integer -> Integer -> Integer
du_'8861'__46 v0 = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0)
-- Once.Arith.Backend.Correct._.run-abstract
d_run'45'abstract_50 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_50 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_274
      (coe v0) (coe v1)
-- Once.Arith.Backend.Correct._.step
d_step_52 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_52 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_106 (coe v0)
      (coe v1)
-- Once.Arith.Backend.Correct.xreg-idx
d_xreg'45'idx_54 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_xreg'45'idx_54 ~v0 ~v1 v2 = du_xreg'45'idx_54 v2
du_xreg'45'idx_54 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
du_xreg'45'idx_54 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.abs-reg-idx
d_abs'45'reg'45'idx_60 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'reg'45'idx_60 = erased
-- Once.Arith.Backend.Correct.exec-xinstr
d_exec'45'xinstr_90 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xinstr_90 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                        (coe du_xreg'45'idx_54 (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                     (coe
                        MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                        (coe du_xreg'45'idx_54 (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_maybe'45'zero_68
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.Shape.d_project_34 (coe v2)
                                 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148
                                    (coe v6)))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_62
                        (coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_54 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v6)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__126 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v6)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v6)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__126 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v6)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_62
                        (coe
                           (\ v8 ->
                              MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe v0) (coe v8) (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_62
                        (coe
                           (\ v8 ->
                              MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
                                (coe v0) (coe v8) (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fadd_214 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fsub_216 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fmul_218 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_62 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fsub_216 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_64 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_62
                        (coe MAlonzo.Code.Once.Float.Arith.d_fneg_248 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_54 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_66 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_62
                        (coe
                           (\ v7 ->
                              MAlonzo.Code.Once.Float.Arith.d_i2f_254
                                (coe v1) (coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe v0) (coe v7))))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_54 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_68 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Float.Decimal.d_round_174 (coe v1) (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_70 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_maybe'45'zero'45'f_72
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Shape.d_projectF_52 (coe v2)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_72 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_54 (coe v4)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog
d_exec'45'xprog_250 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xprog_250 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             d_exec'45'xprog_250 (coe v0) (coe v1) (coe v2) (coe v6)
             (coe d_exec'45'xinstr_90 v0 v1 v2 v5 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.refine-load-imm
d_refine'45'load'45'imm_270 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'imm_270 = erased
-- Once.Arith.Backend.Correct._~_
d__'126'__290 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 -> ()
d__'126'__290 = erased
-- Once.Arith.Backend.Correct.~-refl
d_'126''45'refl_304 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'refl_304 ~v0 ~v1 ~v2 ~v3 = du_'126''45'refl_304
du_'126''45'refl_304 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'refl_304
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.double-write
d_double'45'write_322 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45'write_322 = erased
-- Once.Arith.Backend.Correct.≡→~
d_'8801''8594''126'_366 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8801''8594''126'_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8801''8594''126'_366
du_'8801''8594''126'_366 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8801''8594''126'_366 = coe du_'126''45'refl_304
-- Once.Arith.Backend.Correct.~-sym
d_'126''45'sym_374 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'sym_374 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_'126''45'sym_374 v5
du_'126''45'sym_374 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'sym_374 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.~-trans
d_'126''45'trans_396 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'trans_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'126''45'trans_396 v6 v7
du_'126''45'trans_396 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'trans_396 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              erased)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.refine-load-input
d_refine'45'load'45'input_428 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'input_428 = erased
-- Once.Arith.Backend.Correct.refine-spill
d_refine'45'spill_456 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'spill_456 = erased
-- Once.Arith.Backend.Correct.refine-reload
d_refine'45'reload_484 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'reload_484 = erased
-- Once.Arith.Backend.Correct.refine-move-to-out
d_refine'45'move'45'to'45'out_510 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'move'45'to'45'out_510 = erased
-- Once.Arith.Backend.Correct.⊕-comm
d_'8853''45'comm_530 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'comm_530 = erased
-- Once.Arith.Backend.Correct.⊗-comm
d_'8855''45'comm_540 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'comm_540 = erased
-- Once.Arith.Backend.Correct.norm-absorb-left
d_norm'45'absorb'45'left_550 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'absorb'45'left_550 = erased
-- Once.Arith.Backend.Correct.sub-identity
d_sub'45'identity_562 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'identity_562 = erased
-- Once.Arith.Backend.Correct.bin-op-comm
d_bin'45'op'45'comm_578 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  (Integer -> Integer -> Integer) ->
  (Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'op'45'comm_578 = erased
-- Once.Arith.Backend.Correct.refine-neg
d_refine'45'neg_616 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'neg_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_refine'45'neg_616
du_refine'45'neg_616 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'neg_616
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.xreg-idx-inj
d_xreg'45'idx'45'inj_658 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_658 = erased
-- Once.Arith.Backend.Correct.idx-eq
d_idx'45'eq_668 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idx'45'eq_668 = erased
-- Once.Arith.Backend.Correct.refine-add
d_refine'45'add_700 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'add_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                    ~v12
  = du_refine'45'add_700 v6 v7 v8
du_refine'45'add_700 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'add_700 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_366)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_866 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_866 = erased
-- Once.Arith.Backend.Correct.refine-mul
d_refine'45'mul_904 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'mul_904 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                    ~v12
  = du_refine'45'mul_904 v6 v7 v8
du_refine'45'mul_904 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'mul_904 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_366)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_1070 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_1070 = erased
-- Once.Arith.Backend.Correct.sub-bin-identity
d_sub'45'bin'45'identity_1096 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'bin'45'identity_1096 = erased
-- Once.Arith.Backend.Correct.refine-sub
d_refine'45'sub_1122 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'sub_1122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                     ~v12
  = du_refine'45'sub_1122 v6 v7 v8
du_refine'45'sub_1122 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'sub_1122 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> coe
                                    seq (coe v7)
                                    (coe
                                       seq (coe v8)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                erased))))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢a
d_dst'8802'a_1250 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'a_1250 = erased
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_1300 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_1300 = erased
-- Once.Arith.Backend.Correct.just≢nothing
d_just'8802'nothing_1326 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1326 = erased
-- Once.Arith.Backend.Correct.refine-3addr-just
d_refine'45'3addr'45'just_1346 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'3addr'45'just_1346 = erased
-- Once.Arith.Backend.Correct.refine-div
d_refine'45'div_1394 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'div_1394 = erased
-- Once.Arith.Backend.Correct.refine-rem
d_refine'45'rem_1528 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'rem_1528 = erased
-- Once.Arith.Backend.Correct.refine-div-safe
d_refine'45'div'45'safe_1662 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'div'45'safe_1662 = erased
-- Once.Arith.Backend.Correct.refine-rem-safe
d_refine'45'rem'45'safe_1796 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'rem'45'safe_1796 = erased
-- Once.Arith.Backend.Correct.refine-2addr-just
d_refine'45'2addr'45'just_1928 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'2addr'45'just_1928 = erased
-- Once.Arith.Backend.Correct.refine-shl
d_refine'45'shl_1966 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'shl_1966 = erased
-- Once.Arith.Backend.Correct.refine-sdiv-pow2
d_refine'45'sdiv'45'pow2_2060 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'sdiv'45'pow2_2060 = erased
-- Once.Arith.Backend.Correct.store-cong2
d_store'45'cong2_2154 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'cong2_2154 = erased
-- Once.Arith.Backend.Correct.exec-xinstr-cong
d_exec'45'xinstr'45'cong_2192 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xinstr'45'cong_2192 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_exec'45'xinstr'45'cong_2192 v3 v6
du_exec'45'xinstr'45'cong_2192 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xinstr'45'cong_2192 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           seq (coe v6)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_62 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_64 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           seq (coe v6)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_66 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_68 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_70 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_72 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe v3 (coe du_xreg'45'idx_54 (coe v2))) (coe v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.step-cong
d_step'45'cong_2506 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'45'cong_2506 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_step'45'cong_2506 v3 v6
du_step'45'cong_2506 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'45'cong_2506 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_24 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_26 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_30 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_38 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3 v2)
                                        (coe v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_50 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_52 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog-cong
d_exec'45'xprog'45'cong_2812 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xprog'45'cong_2812 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_exec'45'xprog'45'cong_2812 v3 v6
du_exec'45'xprog'45'cong_2812 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xprog'45'cong_2812 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_exec'45'xprog'45'cong_2812 (coe v3)
             (coe du_exec'45'xinstr'45'cong_2192 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog-++
d_exec'45'xprog'45''43''43'_2830 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'xprog'45''43''43'_2830 = erased
-- Once.Arith.Backend.Correct.InBound
d_InBound_2844 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer -> ()
d_InBound_2844 = erased
-- Once.Arith.Backend.Correct.reg-bound
d_reg'45'bound_2850 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 -> ()
d_reg'45'bound_2850 = erased
-- Once.Arith.Backend.Correct.refine-fadd
d_refine'45'fadd_2868 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'fadd_2868 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fadd_2868 v6 v7 v8
du_refine'45'fadd_2868 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fadd_2868 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_366)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_3034 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_3034 = erased
-- Once.Arith.Backend.Correct.refine-fmul
d_refine'45'fmul_3072 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'fmul_3072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fmul_3072 v6 v7 v8
du_refine'45'fmul_3072 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fmul_3072 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_366)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_3238 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_3238 = erased
-- Once.Arith.Backend.Correct.refine-fneg
d_refine'45'fneg_3272 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'fneg_3272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_refine'45'fneg_3272
du_refine'45'fneg_3272 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fneg_3272
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.refine-load-fimm
d_refine'45'load'45'fimm_3320 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'fimm_3320 = erased
-- Once.Arith.Backend.Correct.refine-fsub
d_refine'45'fsub_3354 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'fsub_3354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fsub_3354 v6 v7 v8
du_refine'45'fsub_3354 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fsub_3354 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_366)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_366)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_3518 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_dst'8802'b_3518 = erased
-- Once.Arith.Backend.Correct.refine-i2f
d_refine'45'i2f_3552 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'i2f_3552 = erased
-- Once.Arith.Backend.Correct.refine-load-finput
d_refine'45'load'45'finput_3592 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'finput_3592 = erased
-- Once.Arith.Backend.Correct.refine
d_refine_3726 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine_3726 ~v0 ~v1 ~v2 v3 v4 ~v5 = du_refine_3726 v3 v4
du_refine_3726 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine_3726 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe du_refine'45'add_700 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe du_refine'45'sub_1122 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe du_refine'45'mul_904 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_366))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_366))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_24 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_366))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_26 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_366))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_366))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_30 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_366))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v4) (coe seq (coe v5) (coe du_refine'45'neg_616))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_38 v2
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_40 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_42 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_366)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe
                                                du_refine'45'fadd_2868 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe
                                                du_refine'45'fsub_3354 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                           -> coe
                                                du_refine'45'fmul_3072 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_50 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v4) (coe seq (coe v5) (coe du_refine'45'fneg_3272))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_52 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v4) (coe seq (coe v5) (coe du_'8801''8594''126'_366))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.All-bound
d_All'45'bound_4070 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] -> ()
d_All'45'bound_4070 = erased
-- Once.Arith.Backend.Correct.refine-program
d_refine'45'program_4082 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'program_4082 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_refine'45'program_4082 v3 v4
du_refine'45'program_4082 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'program_4082 v0 v1
  = case coe v0 of
      [] -> coe du_'126''45'refl_304
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_'126''45'trans_396
                    (coe
                       du_exec'45'xprog'45'cong_2812
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_842
                          (coe v3))
                       (coe du_refine_3726 (coe v2) (coe v4)))
                    (coe du_refine'45'program_4082 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.bound0
d_bound0_4098 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound0_4098 ~v0 ~v1 = du_bound0_4098
du_bound0_4098 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound0_4098
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12) erased
-- Once.Arith.Backend.Correct.bound1
d_bound1_4100 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound1_4100 ~v0 ~v1 = du_bound1_4100
du_bound1_4100 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound1_4100
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14) erased
-- Once.Arith.Backend.Correct.div-instr-bound
d_div'45'instr'45'bound_4104 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Bool -> AgdaAny
d_div'45'instr'45'bound_4104 ~v0 ~v1 v2
  = du_div'45'instr'45'bound_4104 v2
du_div'45'instr'45'bound_4104 :: Bool -> AgdaAny
du_div'45'instr'45'bound_4104 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
            (coe du_bound0_4098)))
-- Once.Arith.Backend.Correct.div-choose-bound
d_div'45'choose'45'bound_4110 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer -> Bool -> AgdaAny
d_div'45'choose'45'bound_4110 ~v0 ~v1 v2 v3
  = du_div'45'choose'45'bound_4110 v2 v3
du_div'45'choose'45'bound_4110 :: Maybe Integer -> Bool -> AgdaAny
du_div'45'choose'45'bound_4110 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
             (coe du_bound1_4100)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_div'45'instr'45'bound_4104 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.div-op-bound
d_div'45'op'45'bound_4122 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_div'45'op'45'bound_4122 ~v0 ~v1 ~v2 v3
  = du_div'45'op'45'bound_4122 v3
du_div'45'op'45'bound_4122 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_div'45'op'45'bound_4122 v0
  = coe
      du_div'45'choose'45'bound_4110
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_94 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_44
         (coe v0))
-- Once.Arith.Backend.Correct.mul-choose-bound
d_mul'45'choose'45'bound_4128 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer -> AgdaAny
d_mul'45'choose'45'bound_4128 ~v0 ~v1 v2
  = du_mul'45'choose'45'bound_4128 v2
du_mul'45'choose'45'bound_4128 :: Maybe Integer -> AgdaAny
du_mul'45'choose'45'bound_4128 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
             (coe du_bound1_4100)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                (coe du_bound0_4098))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.mul-op-bound
d_mul'45'op'45'bound_4136 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_mul'45'op'45'bound_4136 ~v0 ~v1 ~v2 v3
  = du_mul'45'op'45'bound_4136 v3
du_mul'45'op'45'bound_4136 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_mul'45'op'45'bound_4136 v0
  = coe
      du_mul'45'choose'45'bound_4128
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_94 (coe v0))
-- Once.Arith.Backend.Correct.rem-instr-bound
d_rem'45'instr'45'bound_4142 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Bool -> AgdaAny
d_rem'45'instr'45'bound_4142 ~v0 ~v1 v2
  = du_rem'45'instr'45'bound_4142 v2
du_rem'45'instr'45'bound_4142 :: Bool -> AgdaAny
du_rem'45'instr'45'bound_4142 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
            (coe du_bound0_4098)))
-- Once.Arith.Backend.Correct.rem-op-bound
d_rem'45'op'45'bound_4148 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_rem'45'op'45'bound_4148 ~v0 ~v1 ~v2 v3
  = du_rem'45'op'45'bound_4148 v3
du_rem'45'op'45'bound_4148 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_rem'45'op'45'bound_4148 v0
  = coe
      du_rem'45'instr'45'bound_4142
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_44
         (coe v0))
-- Once.Arith.Backend.Correct.All-bound-++
d_All'45'bound'45''43''43'_4156 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_All'45'bound'45''43''43'_4156 ~v0 ~v1 v2 ~v3 v4 v5
  = du_All'45'bound'45''43''43'_4156 v2 v4 v5
du_All'45'bound'45''43''43'_4156 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_All'45'bound'45''43''43'_4156 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_All'45'bound'45''43''43'_4156 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-go-bound
d_compile'45'go'45'bound_4180 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'go'45'bound_4180 ~v0 ~v1 ~v2 v3 v4
  = du_compile'45'go'45'bound_4180 v3 v4
du_compile'45'go'45'bound_4180 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'go'45'bound_4180 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v3 v4
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v3))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                (coe
                   du_All'45'bound'45''43''43'_4156
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      du_compile'45'go'45'bound_4180
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                               (coe du_bound0_4098)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v3 v4
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v3))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                (coe
                   du_All'45'bound'45''43''43'_4156
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      du_compile'45'go'45'bound_4180
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                               (coe du_bound0_4098)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v3 v4
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v3))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                (coe
                   du_All'45'bound'45''43''43'_4156
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      du_compile'45'go'45'bound_4180
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_mul'45'op'45'bound_4136 (coe v4))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_34 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                (coe
                   du_All'45'bound'45''43''43'_4156
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_4180
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_div'45'op'45'bound_4122 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_36 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                (coe
                   du_All'45'bound'45''43''43'_4156
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_4180
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4100)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_rem'45'op'45'bound_4148 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_40 v3
        -> coe
             du_All'45'bound'45''43''43'_4156
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v0) (coe v3))
             (coe du_compile'45'go'45'bound_4180 (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
                   (coe du_bound0_4098))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-abs-bound
d_compile'45'abs'45'bound_4228 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'abs'45'bound_4228 ~v0 ~v1 ~v2 v3
  = du_compile'45'abs'45'bound_4228 v3
du_compile'45'abs'45'bound_4228 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'abs'45'bound_4228 v0
  = coe
      du_All'45'bound'45''43''43'_4156
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_180
         (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe (0 :: Integer))
         (coe v0))
      (coe du_compile'45'go'45'bound_4180 (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4098)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Arith.Backend.Correct.block-correct
d_block'45'correct_4238 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'correct_4238 = erased
