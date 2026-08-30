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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type

-- Once.Arith.Machine.Compile.n-regs
d_n'45'regs_8 :: Integer
d_n'45'regs_8 = coe (2 :: Integer)
-- Once.Arith.Machine.Compile.required-scratch
d_required'45'scratch_14 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
d_required'45'scratch_14 ~v0 ~v1 v2 = du_required'45'scratch_14 v2
du_required'45'scratch_14 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
du_required'45'scratch_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v1
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_14 (coe v2))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_14 (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_14 (coe v2))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_14 (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_14 (coe v2))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_14 (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v2 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_14 (coe v2))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_14 (coe v3)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_required'45'scratch_14 (coe v1))
             (coe
                addInt (coe (1 :: Integer))
                (coe du_required'45'scratch_14 (coe v2)))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v2
        -> coe du_required'45'scratch_14 (coe v2)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v1
        -> coe du_required'45'scratch_14 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.safe-lit?
d_safe'45'lit'63'_40 :: Integer -> Bool
d_safe'45'lit'63'_40 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      -1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.Arith.Machine.Compile.safe-divisor?
d_safe'45'divisor'63'_44 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
d_safe'45'divisor'63'_44 ~v0 v1 = du_safe'45'divisor'63'_44 v1
du_safe'45'divisor'63'_44 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Bool
du_safe'45'divisor'63'_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe d_safe'45'lit'63'_40 (coe v1)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.div-instr
d_div'45'instr_48 ::
  Bool -> MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_div'45'instr_48 v0
  = if coe v0
      then coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_24
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
      else coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
-- Once.Arith.Machine.Compile.rem-instr
d_rem'45'instr_50 ::
  Bool -> MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_rem'45'instr_50 v0
  = if coe v0
      then coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_26
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
      else coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
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
  = coe d_rem'45'instr_50 (coe du_safe'45'divisor'63'_44 (coe v0))
-- Once.Arith.Machine.Compile.pow2-bound
d_pow2'45'bound_58 :: Integer
d_pow2'45'bound_58 = coe (30 :: Integer)
-- Once.Arith.Machine.Compile.pow2-try
d_pow2'45'try_60 :: Integer -> Integer -> Integer -> Maybe Integer
d_pow2'45'try_60 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4
                    = eqInt
                        (coe v2)
                        (coe
                           MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                           (coe v1)) in
              coe
                (if coe v4
                   then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                   else coe
                          d_pow2'45'try_60 (coe v3)
                          (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2)))
-- Once.Arith.Machine.Compile.pow2-exp?
d_pow2'45'exp'63'_88 :: Integer -> Maybe Integer
d_pow2'45'exp'63'_88 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            d_pow2'45'try_60 (coe d_pow2'45'bound_58) (coe (1 :: Integer))
            (coe v0)
      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.Compile.pow2?
d_pow2'63'_94 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Maybe Integer
d_pow2'63'_94 ~v0 v1 = du_pow2'63'_94 v1
du_pow2'63'_94 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Maybe Integer
du_pow2'63'_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1
        -> coe d_pow2'45'exp'63'_88 (coe v1)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.pow2-try-correct
d_pow2'45'try'45'correct_106 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pow2'45'try'45'correct_106 = erased
-- Once.Arith.Machine.Compile.pow2-exp?-correct
d_pow2'45'exp'63''45'correct_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pow2'45'exp'63''45'correct_146 = erased
-- Once.Arith.Machine.Compile.mul-choose
d_mul'45'choose_154 ::
  Maybe Integer ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_mul'45'choose_154 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_28
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.mul-op
d_mul'45'op_160 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_mul'45'op_160 ~v0 v1 = du_mul'45'op_160 v1
du_mul'45'op_160 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
du_mul'45'op_160 v0
  = coe d_mul'45'choose_154 (coe du_pow2'63'_94 (coe v0))
-- Once.Arith.Machine.Compile.div-choose
d_div'45'choose_164 ::
  Maybe Integer ->
  Bool -> MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_div'45'choose_164 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_30
             (coe (0 :: Integer)) (coe (1 :: Integer)) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_div'45'instr_48 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.div-op
d_div'45'op_172 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
d_div'45'op_172 ~v0 v1 = du_div'45'op_172 v1
du_div'45'op_172 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8
du_div'45'op_172 v0
  = coe
      d_div'45'choose_164 (coe du_pow2'63'_94 (coe v0))
      (coe du_safe'45'divisor'63'_44 (coe v0))
-- Once.Arith.Machine.Compile.compile-go
d_compile'45'go_180 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'go_180 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 (coe v4)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_42 (coe v4)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Shape.du_'8970'_'8971''7486'_114
                          (coe v0) (coe v5))
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_40
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.Shape.du_'8970'_'8971''7486'_114
                          (coe v0) (coe v5))
                       (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe du_mul'45'op_160 (coe v6))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe du_div'45'op_172 (coe v6))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                             (coe (0 :: Integer)) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             d_compile'45'go_180 (coe v0) (coe v1)
                             (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_50
                                   (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_compile'45'go_180 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
                      (coe (0 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_compile'45'go_180 (coe v0)
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe du_rem'45'op_54 (coe v5))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_32
                          (coe (0 :: Integer)) (coe (0 :: Integer)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_compile'45'go_180 (coe v0) (coe v1) (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_52
                          (coe (0 :: Integer)) (coe (0 :: Integer)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_compile'45'go_180 (coe v0)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v2) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_54
                   (coe (0 :: Integer)) (coe (0 :: Integer)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Compile.compile-abs
d_compile'45'abs_268 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8]
d_compile'45'abs_268 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         d_compile'45'go_180 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_38
            (coe (0 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Arith.Machine.Compile.fold-div
d_fold'45'div_274 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_fold'45'div_274 ~v0 v1 v2 = du_fold'45'div_274 v1 v2
du_fold'45'div_274 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_fold'45'div_274 v0 v1
  = let v2
          = coe MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v0 v1 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v3
           -> case coe v3 of
                0 -> coe
                       MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 (coe (-1 :: Integer))
                _ | coe geqInt (coe v3) (coe (0 :: Integer)) -> coe v2
                -1 -> coe MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v0
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Compile.fold-mod
d_fold'45'mod_278 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_fold'45'mod_278 ~v0 v1 v2 = du_fold'45'mod_278 v1 v2
du_fold'45'mod_278 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_fold'45'mod_278 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 (coe v0) (coe v1) in
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
d_normalize_298 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_normalize_298 ~v0 v1 = du_normalize_298 v1
du_normalize_298 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_normalize_298 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v1 -> coe v0
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
        -> coe MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v2
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v2 v3
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24
             (coe du_normalize_298 (coe v2)) (coe du_normalize_298 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v2 v3
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28
             (coe du_normalize_298 (coe v2)) (coe du_normalize_298 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v2 v3
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32
             (coe du_normalize_298 (coe v2)) (coe du_normalize_298 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v2 v3
        -> coe
             du_fold'45'div_274 (coe du_normalize_298 (coe v2))
             (coe du_normalize_298 (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v1 v2
        -> coe
             du_fold'45'mod_278 (coe du_normalize_298 (coe v1))
             (coe du_normalize_298 (coe v2))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v2
        -> coe
             MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42
             (coe du_normalize_298 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
