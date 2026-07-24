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
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Backend.Correct._.eval-arith-W
d_eval'45'arith'45'W_12 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_12 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
      (coe v0)
-- Once.Arith.Backend.Correct._._⊕_
d__'8853'__24 :: Integer -> Integer -> Integer -> Integer
d__'8853'__24 v0
  = coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0)
-- Once.Arith.Backend.Correct._._⊖_
d__'8854'__26 :: Integer -> Integer -> Integer -> Integer
d__'8854'__26 v0
  = coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0)
-- Once.Arith.Backend.Correct._._⊗_
d__'8855'__28 :: Integer -> Integer -> Integer -> Integer
d__'8855'__28 v0
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
-- Once.Arith.Backend.Correct._.norm
d_norm_36 :: Integer -> Integer -> Integer
d_norm_36 v0 = coe MAlonzo.Code.Once.Word.d_norm_16 (coe v0)
-- Once.Arith.Backend.Correct._.⊝_
d_'8861'__42 :: Integer -> Integer -> Integer
d_'8861'__42 v0 = coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0)
-- Once.Arith.Backend.Correct._.run-abstract
d_run'45'abstract_46 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_46 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0)
-- Once.Arith.Backend.Correct._.step
d_step_48 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_48 v0
  = coe MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 (coe v0)
-- Once.Arith.Backend.Correct.xreg-idx
d_xreg'45'idx_50 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
d_xreg'45'idx_50 ~v0 v1 = du_xreg'45'idx_50 v1
du_xreg'45'idx_50 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 -> Integer
du_xreg'45'idx_50 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.abs-reg-idx
d_abs'45'reg'45'idx_56 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'reg'45'idx_56 = erased
-- Once.Arith.Backend.Correct.exec-xinstr
d_exec'45'xinstr_86 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xinstr_86 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                        (coe du_xreg'45'idx_50 (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                     (coe
                        MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                        (coe du_xreg'45'idx_50 (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_maybe'45'zero_54
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.Shape.d_project_32 (coe v1)
                                 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148
                                    (coe v5)))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v3)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v3)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v3)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v5))
                           (coe du_xreg'45'idx_50 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v4))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_48
                        (coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v4))
                           (coe du_xreg'45'idx_50 (coe v3)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v4)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__104 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__98 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_bin'45'op_40
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__104 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v5)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_48
                        (coe
                           (\ v7 ->
                              MAlonzo.Code.Once.Word.d_shl'7490'_110 (coe v0) (coe v7) (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v3 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe du_xreg'45'idx_50 (coe v3))
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_un'45'op_48
                        (coe
                           (\ v7 ->
                              MAlonzo.Code.Once.Word.d_sdiv2'7503'_116
                                (coe v0) (coe v7) (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe du_xreg'45'idx_50 (coe v4)))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v4))
                     (coe du_xreg'45'idx_50 (coe v3)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog
d_exec'45'xprog_198 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_exec'45'xprog_198 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             d_exec'45'xprog_198 (coe v0) (coe v1) (coe v5)
             (coe d_exec'45'xinstr_86 v0 v1 v4 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.refine-load-imm
d_refine'45'load'45'imm_218 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'imm_218 = erased
-- Once.Arith.Backend.Correct._~_
d__'126'__238 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 -> ()
d__'126'__238 = erased
-- Once.Arith.Backend.Correct.~-refl
d_'126''45'refl_252 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'refl_252 ~v0 ~v1 ~v2 = du_'126''45'refl_252
du_'126''45'refl_252 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'refl_252
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.double-write
d_double'45'write_270 ::
  Integer ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45'write_270 = erased
-- Once.Arith.Backend.Correct.≡→~
d_'8801''8594''126'_314 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8801''8594''126'_314 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8801''8594''126'_314
du_'8801''8594''126'_314 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8801''8594''126'_314 = coe du_'126''45'refl_252
-- Once.Arith.Backend.Correct.~-sym
d_'126''45'sym_322 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'sym_322 ~v0 ~v1 ~v2 ~v3 v4 = du_'126''45'sym_322 v4
du_'126''45'sym_322 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'sym_322 v0
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
d_'126''45'trans_344 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'126''45'trans_344 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'126''45'trans_344 v5 v6
du_'126''45'trans_344 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'126''45'trans_344 v0 v1
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
d_refine'45'load'45'input_376 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'load'45'input_376 = erased
-- Once.Arith.Backend.Correct.refine-spill
d_refine'45'spill_404 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'spill_404 = erased
-- Once.Arith.Backend.Correct.refine-reload
d_refine'45'reload_432 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'reload_432 = erased
-- Once.Arith.Backend.Correct.refine-move-to-out
d_refine'45'move'45'to'45'out_458 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refine'45'move'45'to'45'out_458 = erased
-- Once.Arith.Backend.Correct.⊕-comm
d_'8853''45'comm_478 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'comm_478 = erased
-- Once.Arith.Backend.Correct.⊗-comm
d_'8855''45'comm_488 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'comm_488 = erased
-- Once.Arith.Backend.Correct.norm-absorb-left
d_norm'45'absorb'45'left_498 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'absorb'45'left_498 = erased
-- Once.Arith.Backend.Correct.sub-identity
d_sub'45'identity_510 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'identity_510 = erased
-- Once.Arith.Backend.Correct.bin-op-comm
d_bin'45'op'45'comm_526 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bin'45'op'45'comm_526 = erased
-- Once.Arith.Backend.Correct.refine-neg
d_refine'45'neg_564 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'neg_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_refine'45'neg_564
du_refine'45'neg_564 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'neg_564
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Arith.Backend.Correct.xreg-idx-inj
d_xreg'45'idx'45'inj_606 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xreg'45'idx'45'inj_606 = erased
-- Once.Arith.Backend.Correct.idx-eq
d_idx'45'eq_616 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idx'45'eq_616 = erased
-- Once.Arith.Backend.Correct.refine-add
d_refine'45'add_648 ::
  Integer ->
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
d_refine'45'add_648 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_refine'45'add_648 v5 v6 v7
du_refine'45'add_648 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'add_648 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_314)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_314)
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
d_dst'8802'b_814 ::
  Integer ->
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
d_dst'8802'b_814 = erased
-- Once.Arith.Backend.Correct.refine-mul
d_refine'45'mul_852 ::
  Integer ->
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
d_refine'45'mul_852 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_refine'45'mul_852 v5 v6 v7
du_refine'45'mul_852 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'mul_852 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_314)
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
                                  (coe v0) (coe v2) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe du_'8801''8594''126'_314)
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
d_dst'8802'b_1018 ::
  Integer ->
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
d_dst'8802'b_1018 = erased
-- Once.Arith.Backend.Correct.sub-bin-identity
d_sub'45'bin'45'identity_1044 ::
  Integer ->
  Maybe Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'bin'45'identity_1044 = erased
-- Once.Arith.Backend.Correct.refine-sub
d_refine'45'sub_1070 ::
  Integer ->
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
d_refine'45'sub_1070 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_refine'45'sub_1070 v5 v6 v7
du_refine'45'sub_1070 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'sub_1070 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d__'8799'x__14
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe seq (coe v5) (coe du_'8801''8594''126'_314)
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
d_dst'8802'a_1198 ::
  Integer ->
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
d_dst'8802'a_1198 = erased
-- Once.Arith.Backend.Correct._.dst≢b
d_dst'8802'b_1248 ::
  Integer ->
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
d_dst'8802'b_1248 = erased
-- Once.Arith.Backend.Correct.just≢nothing
d_just'8802'nothing_1274 ::
  Integer ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1274 = erased
-- Once.Arith.Backend.Correct.refine-3addr-just
d_refine'45'3addr'45'just_1294 ::
  Integer ->
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
d_refine'45'3addr'45'just_1294 = erased
-- Once.Arith.Backend.Correct.refine-div
d_refine'45'div_1342 ::
  Integer ->
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
d_refine'45'div_1342 = erased
-- Once.Arith.Backend.Correct.refine-rem
d_refine'45'rem_1476 ::
  Integer ->
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
d_refine'45'rem_1476 = erased
-- Once.Arith.Backend.Correct.refine-div-safe
d_refine'45'div'45'safe_1610 ::
  Integer ->
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
d_refine'45'div'45'safe_1610 = erased
-- Once.Arith.Backend.Correct.refine-rem-safe
d_refine'45'rem'45'safe_1744 ::
  Integer ->
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
d_refine'45'rem'45'safe_1744 = erased
-- Once.Arith.Backend.Correct.refine-2addr-just
d_refine'45'2addr'45'just_1876 ::
  Integer ->
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
d_refine'45'2addr'45'just_1876 = erased
-- Once.Arith.Backend.Correct.refine-shl
d_refine'45'shl_1914 ::
  Integer ->
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
d_refine'45'shl_1914 = erased
-- Once.Arith.Backend.Correct.refine-sdiv-pow2
d_refine'45'sdiv'45'pow2_2008 ::
  Integer ->
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
d_refine'45'sdiv'45'pow2_2008 = erased
-- Once.Arith.Backend.Correct.store-cong2
d_store'45'cong2_2102 ::
  Integer ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'cong2_2102 = erased
-- Once.Arith.Backend.Correct.exec-xinstr-cong
d_exec'45'xinstr'45'cong_2140 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xinstr'45'cong_2140 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_exec'45'xinstr'45'cong_2140 v2 v5
du_exec'45'xinstr'45'cong_2140 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xinstr'45'cong_2140 v0 v1
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
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v2
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
                                        (coe v3 (coe du_xreg'45'idx_50 (coe v2))) (coe v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.step-cong
d_step'45'cong_2356 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step'45'cong_2356 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_step'45'cong_2356 v2 v5
du_step'45'cong_2356 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step'45'cong_2356 v0 v1
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
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog-cong
d_exec'45'xprog'45'cong_2568 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'xprog'45'cong_2568 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_exec'45'xprog'45'cong_2568 v2 v5
du_exec'45'xprog'45'cong_2568 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'xprog'45'cong_2568 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_exec'45'xprog'45'cong_2568 (coe v3)
             (coe du_exec'45'xinstr'45'cong_2140 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.exec-xprog-++
d_exec'45'xprog'45''43''43'_2586 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'xprog'45''43''43'_2586 = erased
-- Once.Arith.Backend.Correct.InBound
d_InBound_2600 :: Integer -> Integer -> ()
d_InBound_2600 = erased
-- Once.Arith.Backend.Correct.reg-bound
d_reg'45'bound_2606 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 -> ()
d_reg'45'bound_2606 = erased
-- Once.Arith.Backend.Correct.refine
d_refine_2690 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine_2690 ~v0 ~v1 v2 v3 ~v4 = du_refine_2690 v2 v3
du_refine_2690 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine_2690 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_314)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_314)
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
                                           -> coe du_refine'45'add_648 (coe v7) (coe v11) (coe v13)
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
                                           -> coe du_refine'45'sub_1070 (coe v7) (coe v11) (coe v13)
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
                                           -> coe du_refine'45'mul_852 (coe v7) (coe v11) (coe v13)
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_314))
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_314))
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_314))
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
                              seq (coe v7) (coe seq (coe v8) (coe du_'8801''8594''126'_314))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_314))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_30 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v5) (coe seq (coe v6) (coe du_'8801''8594''126'_314))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v4) (coe seq (coe v5) (coe du_refine'45'neg_564))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_314)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 v2 v3
        -> coe seq (coe v1) (coe du_'8801''8594''126'_314)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_38 v2
        -> coe seq (coe v1) (coe du_'8801''8594''126'_314)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.All-bound
d_All'45'bound_2926 ::
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] -> ()
d_All'45'bound_2926 = erased
-- Once.Arith.Backend.Correct.refine-program
d_refine'45'program_2938 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refine'45'program_2938 ~v0 ~v1 v2 v3 ~v4
  = du_refine'45'program_2938 v2 v3
du_refine'45'program_2938 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refine'45'program_2938 v0 v1
  = case coe v0 of
      [] -> coe du_'126''45'refl_252
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_'126''45'trans_344
                    (coe
                       du_exec'45'xprog'45'cong_2568
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen.d_emit'45'program_532
                          (coe v3))
                       (coe du_refine_2690 (coe v2) (coe v4)))
                    (coe du_refine'45'program_2938 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.bound0
d_bound0_2954 :: Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound0_2954 ~v0 = du_bound0_2954
du_bound0_2954 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound0_2954
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12) erased
-- Once.Arith.Backend.Correct.bound1
d_bound1_2956 :: Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bound1_2956 ~v0 = du_bound1_2956
du_bound1_2956 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bound1_2956
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14) erased
-- Once.Arith.Backend.Correct.div-instr-bound
d_div'45'instr'45'bound_2960 :: Integer -> Bool -> AgdaAny
d_div'45'instr'45'bound_2960 ~v0 v1
  = du_div'45'instr'45'bound_2960 v1
du_div'45'instr'45'bound_2960 :: Bool -> AgdaAny
du_div'45'instr'45'bound_2960 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
            (coe du_bound0_2954)))
-- Once.Arith.Backend.Correct.div-choose-bound
d_div'45'choose'45'bound_2966 ::
  Integer -> Maybe Integer -> Bool -> AgdaAny
d_div'45'choose'45'bound_2966 ~v0 v1 v2
  = du_div'45'choose'45'bound_2966 v1 v2
du_div'45'choose'45'bound_2966 :: Maybe Integer -> Bool -> AgdaAny
du_div'45'choose'45'bound_2966 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
             (coe du_bound1_2956)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_div'45'instr'45'bound_2960 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.div-op-bound
d_div'45'op'45'bound_2978 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_div'45'op'45'bound_2978 ~v0 ~v1 v2
  = du_div'45'op'45'bound_2978 v2
du_div'45'op'45'bound_2978 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_div'45'op'45'bound_2978 v0
  = coe
      du_div'45'choose'45'bound_2966
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_90 (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_40
         (coe v0))
-- Once.Arith.Backend.Correct.mul-choose-bound
d_mul'45'choose'45'bound_2984 ::
  Integer -> Maybe Integer -> AgdaAny
d_mul'45'choose'45'bound_2984 ~v0 v1
  = du_mul'45'choose'45'bound_2984 v1
du_mul'45'choose'45'bound_2984 :: Maybe Integer -> AgdaAny
du_mul'45'choose'45'bound_2984 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
             (coe du_bound1_2956)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                (coe du_bound0_2954))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.mul-op-bound
d_mul'45'op'45'bound_2992 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_mul'45'op'45'bound_2992 ~v0 ~v1 v2
  = du_mul'45'op'45'bound_2992 v2
du_mul'45'op'45'bound_2992 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_mul'45'op'45'bound_2992 v0
  = coe
      du_mul'45'choose'45'bound_2984
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_pow2'63'_90 (coe v0))
-- Once.Arith.Backend.Correct.rem-instr-bound
d_rem'45'instr'45'bound_2998 :: Integer -> Bool -> AgdaAny
d_rem'45'instr'45'bound_2998 ~v0 v1
  = du_rem'45'instr'45'bound_2998 v1
du_rem'45'instr'45'bound_2998 :: Bool -> AgdaAny
du_rem'45'instr'45'bound_2998 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
            (coe du_bound0_2954)))
-- Once.Arith.Backend.Correct.rem-op-bound
d_rem'45'op'45'bound_3004 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_rem'45'op'45'bound_3004 ~v0 ~v1 v2
  = du_rem'45'op'45'bound_3004 v2
du_rem'45'op'45'bound_3004 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_rem'45'op'45'bound_3004 v0
  = coe
      du_rem'45'instr'45'bound_2998
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_safe'45'divisor'63'_40
         (coe v0))
-- Once.Arith.Backend.Correct.All-bound-++
d_All'45'bound'45''43''43'_3012 ::
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
d_All'45'bound'45''43''43'_3012 ~v0 v1 ~v2 v3 v4
  = du_All'45'bound'45''43''43'_3012 v1 v3 v4
du_All'45'bound'45''43''43'_3012 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  AgdaAny -> AgdaAny -> AgdaAny
du_All'45'bound'45''43''43'_3012 v0 v1 v2
  = case coe v0 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe du_All'45'bound'45''43''43'_3012 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-go-bound
d_compile'45'go'45'bound_3036 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'go'45'bound_3036 ~v0 ~v1 v2 v3
  = du_compile'45'go'45'bound_3036 v2 v3
du_compile'45'go'45'bound_3036 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'go'45'bound_3036 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                (coe
                   du_All'45'bound'45''43''43'_3012
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_3036
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                               (coe du_bound0_2954)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                (coe
                   du_All'45'bound'45''43''43'_3012
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_3036
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                               (coe du_bound0_2954)))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                (coe
                   du_All'45'bound'45''43''43'_3012
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_3036
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_mul'45'op'45'bound_2992 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                (coe
                   du_All'45'bound'45''43''43'_3012
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_3036
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_div'45'op'45'bound_2978 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v2 v3
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                (coe
                   du_All'45'bound'45''43''43'_3012
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      du_compile'45'go'45'bound_3036
                      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound1_2956)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_rem'45'op'45'bound_3004 (coe v3))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v2
        -> coe
             du_All'45'bound'45''43''43'_3012
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
                (coe v0) (coe v2))
             (coe du_compile'45'go'45'bound_3036 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
                   (coe du_bound0_2954))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.Correct.compile-abs-bound
d_compile'45'abs'45'bound_3084 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
d_compile'45'abs'45'bound_3084 ~v0 ~v1 v2
  = du_compile'45'abs'45'bound_3084 v2
du_compile'45'abs'45'bound_3084 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny
du_compile'45'abs'45'bound_3084 v0
  = coe
      du_All'45'bound'45''43''43'_3012
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe (0 :: Integer)) (coe v0))
      (coe du_compile'45'go'45'bound_3036 (coe (0 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe du_bound0_2954)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Arith.Backend.Correct.block-correct
d_block'45'correct_3094 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'correct_3094 = erased
