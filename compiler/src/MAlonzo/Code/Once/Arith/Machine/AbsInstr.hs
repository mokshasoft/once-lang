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
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.AbsInstr.AbstractInstr
d_AbstractInstr_8 = ()
data T_AbstractInstr_8
  = C_load'45'input_10 [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22]
                       Integer |
    C_load'45'imm_12 Integer Integer |
    C_add'45'rrr_14 Integer Integer Integer |
    C_sub'45'rrr_16 Integer Integer Integer |
    C_mul'45'rrr_18 Integer Integer Integer |
    C_neg'45'rr_20 Integer Integer | C_spill_22 Integer Integer |
    C_reload_24 Integer Integer | C_move'45'to'45'out_26 Integer
-- Once.Arith.Machine.AbsInstr.bin-op
d_bin'45'op_28 ::
  (Integer -> Integer -> Integer) ->
  Maybe Integer -> Maybe Integer -> Maybe Integer
d_bin'45'op_28 v0 v1 v2
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
d_un'45'op_36 ::
  (Integer -> Integer) -> Maybe Integer -> Maybe Integer
d_un'45'op_36 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.maybe-zero
d_maybe'45'zero_42 :: Maybe Integer -> Integer
d_maybe'45'zero_42 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.step
d_step_48 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_step_48 v0 v1
  = case coe v1 of
      C_load'45'input_10 v2 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                     (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer))
                           (coe
                              d_maybe'45'zero_42
                              (coe
                                 MAlonzo.Code.Once.Arith.Machine.AbsState.d_project_32 (coe v0)
                                 (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188
                                    (coe v4)))))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v4)))
      C_load'45'imm_12 v2 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                     (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Once.Word.d_fromℤ_18 (coe (64 :: Integer)) (coe v2))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v4)))
      C_add'45'rrr_14 v2 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                     (coe v2)
                     (coe
                        d_bin'45'op_28
                        (coe MAlonzo.Code.Once.Word.d__'8853'__24 (coe (64 :: Integer)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v3))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v5)))
      C_sub'45'rrr_16 v2 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                     (coe v2)
                     (coe
                        d_bin'45'op_28
                        (coe MAlonzo.Code.Once.Word.d__'8854'__30 (coe (64 :: Integer)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v3))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v5)))
      C_mul'45'rrr_18 v2 v3 v4
        -> coe
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                     (coe v2)
                     (coe
                        d_bin'45'op_28
                        (coe MAlonzo.Code.Once.Word.d__'8855'__36 (coe (64 :: Integer)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v3))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v5))
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v5))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v5)))
      C_neg'45'rr_20 v2 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                     (coe v2)
                     (coe
                        d_un'45'op_36
                        (coe MAlonzo.Code.Once.Word.d_'8861'__42 (coe (64 :: Integer)))
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                           (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                           (coe v3))))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v4)))
      C_spill_22 v2 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                        (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                        (coe v2)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v4)))
      C_reload_24 v2 v3
        -> coe
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'8614'_'93'_54
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v4))
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                        (coe v2)))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_output_186 (coe v4))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v4)))
      C_move'45'to'45'out_26 v2
        -> coe
             (\ v3 ->
                coe
                  MAlonzo.Code.Once.Arith.Machine.AbsState.C_mk'45'state_190
                  (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_scratch_184 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d__'91'_'93'_84
                     (coe MAlonzo.Code.Once.Arith.Machine.AbsState.d_regs_182 (coe v3))
                     (coe v2))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.AbsState.d_input_188 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsInstr.run-abstract
d_run'45'abstract_112 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  [T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_170
d_run'45'abstract_112 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             d_run'45'abstract_112 (coe v0) (coe v4) (coe d_step_48 v0 v3 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
