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
import qualified MAlonzo.Code.Once.Arith.CmpOp
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
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_296
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
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_110 (coe v0)
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
                              MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_maybe'45'zero_72
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_66
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v4 v5 v6 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v8))
                     (coe du_xreg'45'idx_54 (coe v5))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe
                           MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'bit_62 (coe v0) (coe v4))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v8))
                           (coe du_xreg'45'idx_54 (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v8))
                           (coe du_xreg'45'idx_54 (coe v7)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v8))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v8))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v8)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_66
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_66
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe MAlonzo.Code.Once.Float.Arith.d_fadd_314 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe MAlonzo.Code.Once.Float.Arith.d_fsub_316 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe MAlonzo.Code.Once.Float.Arith.d_fmul_318 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe MAlonzo.Code.Once.Float.Arith.d_fdiv_320 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_58
                        (coe MAlonzo.Code.Once.Float.Arith.d_fsub_316 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_66
                        (coe MAlonzo.Code.Once.Float.Arith.d_fneg_356 (coe v1))
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_54 (coe v4))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_66
                        (coe
                           (\ v7 ->
                              MAlonzo.Code.Once.Float.Arith.d_i2f_362
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v4 v5
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v4 v5
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
                           MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_maybe'45'zero'45'f_76
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v4
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
d_exec'45'xprog_268 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xprog_268 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             d_exec'45'xprog_268 (coe v0) (coe v1) (coe v2) (coe v6)
             (coe d_exec'45'xinstr_90 v0 v1 v2 v5 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.refine-load-imm
d_refine'45'load'45'imm_288 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'imm_288 = erased
-- Once.Arith.Backend.Correct._~_
d__'126'__308 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 -> ()
d__'126'__308 = erased
-- Once.Arith.Backend.Correct.~-refl
d_'126''45'refl_322 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'refl_322 ~v0 ~v1 ~v2 ~v3 = du_'126''45'refl_322
du_'126''45'refl_322 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'refl_322
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.double-write
d_double'45'write_340 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45'write_340 = erased
-- Once.Arith.Backend.Correct.≡→~
d_'8801''8594''126'_384 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8801''8594''126'_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8801''8594''126'_384
du_'8801''8594''126'_384 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8801''8594''126'_384 = coe du_'126''45'refl_322
-- Once.Arith.Backend.Correct.~-sym
d_'126''45'sym_392 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'sym_392 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_'126''45'sym_392 v5
du_'126''45'sym_392 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'sym_392 v0
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
d_'126''45'trans_414 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'trans_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'126''45'trans_414 v6 v7
du_'126''45'trans_414 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'trans_414 v0 v1
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
d_refine'45'load'45'input_446 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'input_446 = erased
-- Once.Arith.Backend.Correct.refine-spill
d_refine'45'spill_474 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'spill_474 = erased
-- Once.Arith.Backend.Correct.refine-reload
d_refine'45'reload_502 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'reload_502 = erased
-- Once.Arith.Backend.Correct.refine-move-to-out
d_refine'45'move'45'to'45'out_528 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'move'45'to'45'out_528 = erased
-- Once.Arith.Backend.Correct.⊕-comm
d_'8853''45'comm_548 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'comm_548 = erased
-- Once.Arith.Backend.Correct.⊗-comm
d_'8855''45'comm_558 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'comm_558 = erased
-- Once.Arith.Backend.Correct.norm-absorb-left
d_norm'45'absorb'45'left_568 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'absorb'45'left_568 = erased
-- Once.Arith.Backend.Correct.sub-identity
d_sub'45'identity_580 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'identity_580 = erased
-- Once.Arith.Backend.Correct.bin-op-comm
d_bin'45'op'45'comm_596 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  (Integer -> Integer -> Integer) ->
  (Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'op'45'comm_596 = erased
-- Once.Arith.Backend.Correct.refine-neg
d_refine'45'neg_634 ::
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
d_refine'45'neg_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_refine'45'neg_634
du_refine'45'neg_634 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'neg_634
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.xreg-idx-inj
d_xreg'45'idx'45'inj_676 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_676 = erased
-- Once.Arith.Backend.Correct.idx-eq
d_idx'45'eq_686 ::
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
d_idx'45'eq_686 = erased
-- Once.Arith.Backend.Correct.refine-add
d_refine'45'add_718 ::
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
d_refine'45'add_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                    ~v12
  = du_refine'45'add_718 v6 v7 v8
du_refine'45'add_718 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'add_718 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_384)
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
d_dst'8802'b_884 ::
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
d_dst'8802'b_884 = erased
-- Once.Arith.Backend.Correct.refine-mul
d_refine'45'mul_922 ::
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
d_refine'45'mul_922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                    ~v12
  = du_refine'45'mul_922 v6 v7 v8
du_refine'45'mul_922 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'mul_922 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_384)
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
d_dst'8802'b_1088 ::
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
d_dst'8802'b_1088 = erased
-- Once.Arith.Backend.Correct.sub-bin-identity
d_sub'45'bin'45'identity_1114 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'bin'45'identity_1114 = erased
-- Once.Arith.Backend.Correct.refine-sub
d_refine'45'sub_1140 ::
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
d_refine'45'sub_1140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10 ~v11
                     ~v12
  = du_refine'45'sub_1140 v6 v7 v8
du_refine'45'sub_1140 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'sub_1140 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
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
d_dst'8802'a_1268 ::
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
d_dst'8802'a_1268 = erased
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_1318 ::
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
d_dst'8802'b_1318 = erased
-- Once.Arith.Backend.Correct.just≢nothing
d_just'8802'nothing_1344 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1344 = erased
-- Once.Arith.Backend.Correct.refine-3addr-just
d_refine'45'3addr'45'just_1364 ::
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
d_refine'45'3addr'45'just_1364 = erased
-- Once.Arith.Backend.Correct.refine-div
d_refine'45'div_1412 ::
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
d_refine'45'div_1412 = erased
-- Once.Arith.Backend.Correct.refine-fdiv
d_refine'45'fdiv_1546 ::
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
d_refine'45'fdiv_1546 = erased
-- Once.Arith.Backend.Correct.refine-cmp
d_refine'45'cmp_1682 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
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
d_refine'45'cmp_1682 = erased
-- Once.Arith.Backend.Correct.refine-rem
d_refine'45'rem_1826 ::
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
d_refine'45'rem_1826 = erased
-- Once.Arith.Backend.Correct.refine-div-safe
d_refine'45'div'45'safe_1960 ::
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
d_refine'45'div'45'safe_1960 = erased
-- Once.Arith.Backend.Correct.refine-rem-safe
d_refine'45'rem'45'safe_2094 ::
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
d_refine'45'rem'45'safe_2094 = erased
-- Once.Arith.Backend.Correct.refine-2addr-just
d_refine'45'2addr'45'just_2226 ::
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
d_refine'45'2addr'45'just_2226 = erased
-- Once.Arith.Backend.Correct.refine-shl
d_refine'45'shl_2264 ::
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
d_refine'45'shl_2264 = erased
-- Once.Arith.Backend.Correct.refine-sdiv-pow2
d_refine'45'sdiv'45'pow2_2358 ::
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
d_refine'45'sdiv'45'pow2_2358 = erased
-- Once.Arith.Backend.Correct.store-cong2
d_store'45'cong2_2452 ::
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
d_store'45'cong2_2452 = erased
-- Once.Arith.Backend.Correct.exec-xinstr-cong
d_exec'45'xinstr'45'cong_2490 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xinstr'45'cong_2490 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_exec'45'xinstr'45'cong_2490 v3 v6
du_exec'45'xinstr'45'cong_2490 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xinstr'45'cong_2490 v0 v1
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xcmp'45'rrr_48 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_50 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_52 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_54 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_56 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_58 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_60 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_62 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_64 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_66 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_68 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           seq (coe v6)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_70 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_72 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_74 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_76 v2
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
d_step'45'cong_2834 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'45'cong_2834 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_step'45'cong_2834 v3 v6
du_step'45'cong_2834 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'45'cong_2834 v0 v1
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
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_cmp'45'rrr_24 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_26 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_30 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_32 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_34 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36 v2 v3
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
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_40 v2
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
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_46 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_48 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_50 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_52 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           seq (coe v8)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_54 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           seq (coe v7)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_56 v2 v3
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
d_exec'45'xprog'45'cong_3170 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xprog'45'cong_3170 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_exec'45'xprog'45'cong_3170 v3 v6
du_exec'45'xprog'45'cong_3170 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xprog'45'cong_3170 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_exec'45'xprog'45'cong_3170 (coe v3)
             (coe du_exec'45'xinstr'45'cong_2490 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog-++
d_exec'45'xprog'45''43''43'_3188 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'xprog'45''43''43'_3188 = erased
-- Once.Arith.Backend.Correct.InBound
d_InBound_3202 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer -> ()
d_InBound_3202 = erased
-- Once.Arith.Backend.Correct.reg-bound
d_reg'45'bound_3208 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 -> ()
d_reg'45'bound_3208 = erased
-- Once.Arith.Backend.Correct.refine-fadd
d_refine'45'fadd_3226 ::
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
d_refine'45'fadd_3226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fadd_3226 v6 v7 v8
du_refine'45'fadd_3226 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fadd_3226 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_384)
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
d_dst'8802'b_3392 ::
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
d_dst'8802'b_3392 = erased
-- Once.Arith.Backend.Correct.refine-fmul
d_refine'45'fmul_3430 ::
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
d_refine'45'fmul_3430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fmul_3430 v6 v7 v8
du_refine'45'fmul_3430 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fmul_3430 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_384)
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
d_dst'8802'b_3596 ::
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
d_dst'8802'b_3596 = erased
-- Once.Arith.Backend.Correct.refine-fneg
d_refine'45'fneg_3630 ::
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
d_refine'45'fneg_3630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_refine'45'fneg_3630
du_refine'45'fneg_3630 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fneg_3630
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.refine-load-fimm
d_refine'45'load'45'fimm_3678 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'fimm_3678 = erased
-- Once.Arith.Backend.Correct.refine-fsub
d_refine'45'fsub_3712 ::
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
d_refine'45'fsub_3712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
                      ~v11 ~v12
  = du_refine'45'fsub_3712 v6 v7 v8
du_refine'45'fsub_3712 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'fsub_3712 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_384)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_384)
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
d_dst'8802'b_3876 ::
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
d_dst'8802'b_3876 = erased
-- Once.Arith.Backend.Correct.refine-i2f
d_refine'45'i2f_3910 ::
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
d_refine'45'i2f_3910 = erased
-- Once.Arith.Backend.Correct.refine-load-finput
d_refine'45'load'45'finput_3950 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'finput_3950 = erased
-- Once.Arith.Backend.Correct.refine
d_refine_4098 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine_4098 ~v0 ~v1 ~v2 v3 v4 ~v5 = du_refine_4098 v3 v4
du_refine_4098 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine_4098 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
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
                                           -> coe du_refine'45'add_718 (coe v7) (coe v11) (coe v13)
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
                                           -> coe du_refine'45'sub_1140 (coe v7) (coe v11) (coe v13)
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
                                           -> coe du_refine'45'mul_922 (coe v7) (coe v11) (coe v13)
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_384))
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_384))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_cmp'45'rrr_24 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    seq (coe v6)
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> coe
                              seq (coe v8) (coe seq (coe v9) (coe du_'8801''8594''126'_384))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_26 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_384))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_384))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_30 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_384))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_32 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_384))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_34 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v4) (coe seq (coe v5) (coe du_refine'45'neg_634))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_40 v2
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_42 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_44 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_384)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_46 v2 v3 v4
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
                                                du_refine'45'fadd_3226 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_48 v2 v3 v4
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
                                                du_refine'45'fsub_3712 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_50 v2 v3 v4
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
                                                du_refine'45'fmul_3430 (coe v7) (coe v11) (coe v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_52 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_384))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_54 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v4) (coe seq (coe v5) (coe du_refine'45'fneg_3630))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_56 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v4) (coe seq (coe v5) (coe du_'8801''8594''126'_384))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.All-bound
d_All'45'bound_4484 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] -> ()
d_All'45'bound_4484 = erased
-- Once.Arith.Backend.Correct.refine-program
d_refine'45'program_4496 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'program_4496 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_refine'45'program_4496 v3 v4
du_refine'45'program_4496 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'program_4496 v0 v1
  = case coe v0 of
      [] -> coe du_'126''45'refl_322
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_'126''45'trans_414
                    (coe
                       du_exec'45'xprog'45'cong_3170
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_904
                          (coe v3))
                       (coe du_refine_4098 (coe v2) (coe v4)))
                    (coe du_refine'45'program_4496 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.bound0
d_bound0_4512 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound0_4512 ~v0 ~v1 = du_bound0_4512
du_bound0_4512 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound0_4512
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12) erased
-- Once.Arith.Backend.Correct.bound1
d_bound1_4514 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound1_4514 ~v0 ~v1 = du_bound1_4514
du_bound1_4514 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound1_4514
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14) erased
-- Once.Arith.Backend.Correct.div-instr-bound
d_div'45'instr'45'bound_4518 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Bool -> AgdaAny
d_div'45'instr'45'bound_4518 ~v0 ~v1 v2
  = du_div'45'instr'45'bound_4518 v2
du_div'45'instr'45'bound_4518 :: Bool -> AgdaAny
du_div'45'instr'45'bound_4518 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
            (coe du_bound0_4512)))
-- Once.Arith.Backend.Correct.div-choose-bound
d_div'45'choose'45'bound_4524 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer -> Bool -> AgdaAny
d_div'45'choose'45'bound_4524 ~v0 ~v1 v2 v3
  = du_div'45'choose'45'bound_4524 v2 v3
du_div'45'choose'45'bound_4524 :: Maybe Integer -> Bool -> AgdaAny
du_div'45'choose'45'bound_4524 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
             (coe du_bound1_4514)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_div'45'instr'45'bound_4518 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.div-op-bound
d_div'45'op'45'bound_4536 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_div'45'op'45'bound_4536 ~v0 ~v1 ~v2 v3
  = du_div'45'op'45'bound_4536 v3
du_div'45'op'45'bound_4536 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_div'45'op'45'bound_4536 v0
  = coe
      du_div'45'choose'45'bound_4524
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_98 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_48
         (coe v0))
-- Once.Arith.Backend.Correct.mul-choose-bound
d_mul'45'choose'45'bound_4542 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Maybe Integer -> AgdaAny
d_mul'45'choose'45'bound_4542 ~v0 ~v1 v2
  = du_mul'45'choose'45'bound_4542 v2
du_mul'45'choose'45'bound_4542 :: Maybe Integer -> AgdaAny
du_mul'45'choose'45'bound_4542 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
             (coe du_bound1_4514)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                (coe du_bound0_4512))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.mul-op-bound
d_mul'45'op'45'bound_4550 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_mul'45'op'45'bound_4550 ~v0 ~v1 ~v2 v3
  = du_mul'45'op'45'bound_4550 v3
du_mul'45'op'45'bound_4550 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_mul'45'op'45'bound_4550 v0
  = coe
      du_mul'45'choose'45'bound_4542
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_98 (coe v0))
-- Once.Arith.Backend.Correct.rem-instr-bound
d_rem'45'instr'45'bound_4556 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Bool -> AgdaAny
d_rem'45'instr'45'bound_4556 ~v0 ~v1 v2
  = du_rem'45'instr'45'bound_4556 v2
du_rem'45'instr'45'bound_4556 :: Bool -> AgdaAny
du_rem'45'instr'45'bound_4556 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
            (coe du_bound0_4512)))
-- Once.Arith.Backend.Correct.rem-op-bound
d_rem'45'op'45'bound_4562 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_rem'45'op'45'bound_4562 ~v0 ~v1 ~v2 v3
  = du_rem'45'op'45'bound_4562 v3
du_rem'45'op'45'bound_4562 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_rem'45'op'45'bound_4562 v0
  = coe
      du_rem'45'instr'45'bound_4556
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_48
         (coe v0))
-- Once.Arith.Backend.Correct.All-bound-++
d_All'45'bound'45''43''43'_4570 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_All'45'bound'45''43''43'_4570 ~v0 ~v1 v2 ~v3 v4 v5
  = du_All'45'bound'45''43''43'_4570 v2 v4 v5
du_All'45'bound'45''43''43'_4570 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_All'45'bound'45''43''43'_4570 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_All'45'bound'45''43''43'_4570 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-go-bound
d_compile'45'go'45'bound_4594 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'go'45'bound_4594 ~v0 ~v1 v2 v3 v4
  = du_compile'45'go'45'bound_4594 v2 v3 v4
du_compile'45'go'45'bound_4594 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'go'45'bound_4594 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v4 v5
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                               (coe du_bound0_4512)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v4 v5
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                               (coe du_bound0_4512)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v4 v5
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_mul'45'op'45'bound_4550 (coe v5))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v4 v5
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_div'45'op'45'bound_4536 (coe v5))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v3 v4
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v3))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v4))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_rem'45'op'45'bound_4562 (coe v4))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v4
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                   (coe du_bound0_4512))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v3 v4 v5
        -> coe
             du_All'45'bound'45''43''43'_4570
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v1)
                (coe v4))
             (coe du_compile'45'go'45'bound_4594 (coe v0) (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                (coe
                   du_All'45'bound'45''43''43'_4570
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
                      (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      du_compile'45'go'45'bound_4594 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_4514)
                               (coe du_bound0_4512)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-abs-bound
d_compile'45'abs'45'bound_4650 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'abs'45'bound_4650 ~v0 ~v1 v2 v3
  = du_compile'45'abs'45'bound_4650 v2 v3
du_compile'45'abs'45'bound_4650 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'abs'45'bound_4650 v0 v1
  = coe
      du_All'45'bound'45''43''43'_4570
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v0) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe (0 :: Integer)) (coe v1))
      (coe
         du_compile'45'go'45'bound_4594 (coe v0) (coe (0 :: Integer))
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_4512)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Arith.Backend.Correct.block-correct
d_block'45'correct_4660 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'correct_4660 = erased
