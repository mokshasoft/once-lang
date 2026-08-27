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

module MAlonzo.Code.Once.Arith.Machine.AbsInstr where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.AbsInstr.AbstractInstr
d_AbstractInstr_8 = ()
data T_AbstractInstr_8
  = C_load'45'input_10 [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
                       Integer |
    C_load'45'imm_12 Integer Integer |
    C_add'45'rrr_14 Integer Integer Integer |
    C_sub'45'rrr_16 Integer Integer Integer |
    C_mul'45'rrr_18 Integer Integer Integer |
    C_div'45'rrr_20 Integer Integer Integer |
    C_rem'45'rrr_22 Integer Integer Integer |
    C_div'45'safe'45'rrr_24 Integer Integer Integer |
    C_rem'45'safe'45'rrr_26 Integer Integer Integer |
    C_shl'45'rri_28 Integer Integer Integer |
    C_sdiv'45'pow2'45'rri_30 Integer Integer Integer |
    C_neg'45'rr_32 Integer Integer | C_spill_34 Integer Integer |
    C_reload_36 Integer Integer | C_move'45'to'45'out_38 Integer |
    C_load'45'finput_40 [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24]
                        Integer |
    C_load'45'fimm_42 MAlonzo.Code.Once.Float.Decimal.T_Decimal_6
                      Integer |
    C_fadd'45'rrr_44 Integer Integer Integer |
    C_fsub'45'rrr_46 Integer Integer Integer |
    C_fmul'45'rrr_48 Integer Integer Integer |
    C_fneg'45'rr_50 Integer Integer | C_i2f'45'rr_52 Integer Integer
-- Once.Arith.Machine.AbsInstr.bin-op
d_bin'45'op_54 ::
  (Integer -> Integer -> Integer) ->
  Maybe Integer -> Maybe Integer -> Maybe Integer
d_bin'45'op_54 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.un-op
d_un'45'op_62 ::
  (Integer -> Integer) -> Maybe Integer -> Maybe Integer
d_un'45'op_62 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.maybe-zero
d_maybe'45'zero_68 :: Maybe Integer -> Integer
d_maybe'45'zero_68 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.maybe-zero-f
d_maybe'45'zero'45'f_72 :: Maybe Integer -> Integer
d_maybe'45'zero'45'f_72 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.Exec.step
d_step_106 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_106 v0 v1 v2 v3
  = case coe v3 of
      C_load'45'input_10 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0)
                           (coe
                              d_maybe'45'zero_68
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.Shape.d_project_34 (coe v2)
                                 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148
                                    (coe v6)))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_load'45'imm_12 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_add'45'rrr_14 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54 (coe MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_sub'45'rrr_16 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54 (coe MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_mul'45'rrr_18 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54 (coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_div'45'rrr_20 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_rem'45'rrr_22 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__126 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_div'45'safe'45'rrr_24 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_rem'45'safe'45'rrr_26 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Word.d__'37''738'__126 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_shl'45'rri_28 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_un'45'op_62
                        (coe
                           (\ v8 ->
                              MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe v0) (coe v8) (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_sdiv'45'pow2'45'rri_30 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_un'45'op_62
                        (coe
                           (\ v8 ->
                              MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
                                (coe v0) (coe v8) (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_neg'45'rr_32 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v4)
                     (coe
                        d_un'45'op_62 (coe MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_spill_34 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_reload_36 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_move'45'to'45'out_38 v4
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
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v5)))
      C_load'45'finput_40 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           d_maybe'45'zero'45'f_72
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Shape.d_projectF_52 (coe v2)
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_load'45'fimm_42 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v5)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Float.Decimal.d_round_174 (coe v1) (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_fadd'45'rrr_44 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fadd_214 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_fsub'45'rrr_46 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fsub_216 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_fmul'45'rrr_48 v4 v5 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                     (coe v4)
                     (coe
                        d_bin'45'op_54
                        (coe MAlonzo.Code.Once.Float.Arith.d_fmul_218 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v7))
                           (coe v6))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v7))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v7)))
      C_fneg'45'rr_50 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v4)
                     (coe
                        d_un'45'op_62
                        (coe MAlonzo.Code.Once.Float.Arith.d_fneg_248 (coe v1))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      C_i2f'45'rr_52 v4 v5
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_150
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_14
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                     (coe v4)
                     (coe
                        d_un'45'op_62
                        (coe
                           (\ v7 ->
                              MAlonzo.Code.Once.Float.Arith.d_i2f_254
                                (coe v1) (coe MAlonzo.Code.Once.Word.d_toℤ_50 (coe v0) (coe v7))))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_44
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_142 (coe v6))
                           (coe v5))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_144 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_146 (coe v6))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_148 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.Exec.run-abstract
d_run'45'abstract_274 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_274 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             d_run'45'abstract_274 (coe v0) (coe v1) (coe v2) (coe v6)
             (coe d_step_106 v0 v1 v2 v5 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
