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

module MAlonzo.Code.Once.Arith.Machine.CompileCorrect where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.CompileCorrect._.run-abstract
d_run'45'abstract_14 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_14 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1)
-- Once.Arith.Machine.CompileCorrect._.step
d_step_16 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_16 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 (coe v0)
      (coe v1)
-- Once.Arith.Machine.CompileCorrect._._/ˢ_
d__'47''738'__22 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d__'47''738'__22 v0 ~v1 = du__'47''738'__22 v0
du__'47''738'__22 :: Integer -> Integer -> Integer -> Integer
du__'47''738'__22 v0
  = coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0)
-- Once.Arith.Machine.CompileCorrect._._⊗_
d__'8855'__28 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d__'8855'__28 v0 ~v1 = du__'8855'__28 v0
du__'8855'__28 :: Integer -> Integer -> Integer -> Integer
du__'8855'__28 v0
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.fromℤ
d_fromℤ_42 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer
d_fromℤ_42 v0 ~v1 = du_fromℤ_42 v0
du_fromℤ_42 :: Integer -> Integer -> Integer
du_fromℤ_42 v0 = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.modulus
d_modulus_50 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> Integer
d_modulus_50 v0 ~v1 = du_modulus_50 v0
du_modulus_50 :: Integer -> Integer
du_modulus_50 v0 = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.sdiv2ᵏ
d_sdiv2'7503'_54 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_54 v0 ~v1 = du_sdiv2'7503'_54 v0
du_sdiv2'7503'_54 :: Integer -> Integer -> Integer -> Integer
du_sdiv2'7503'_54 v0
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.shlᵂ
d_shl'7490'_56 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> Integer -> Integer
d_shl'7490'_56 v0 ~v1 = du_shl'7490'_56 v0
du_shl'7490'_56 :: Integer -> Integer -> Integer -> Integer
du_shl'7490'_56 v0
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.eval-arith-W
d_eval'45'arith'45'W_66 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_66 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
      (coe v0) (coe v1)
-- Once.Arith.Machine.CompileCorrect.step-div-safe≡
d_step'45'div'45'safe'8801'_72 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'safe'8801'_72 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-instr
d_step'45'div'45'instr_82 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'instr_82 = erased
-- Once.Arith.Machine.CompileCorrect.step-mul-op-eq
d_step'45'mul'45'op'45'eq_96 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mul'45'op'45'eq_96 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_126 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_128 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_134 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-op-eq
d_step'45'div'45'op'45'eq_230 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'op'45'eq_230 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_260 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_260 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_262 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_262 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_268 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_268 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-instr
d_step'45'rem'45'instr_362 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'instr_362 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-op
d_step'45'rem'45'op_374 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'op_374 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv
d_CompileGoInv_390 a0 a1 a2 a3 a4 a5 a6 = ()
data T_CompileGoInv_390 = C_constructor_422
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.reg0
d_reg0_412 ::
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg0_412 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.scratch≤
d_scratch'8804'_416 ::
  T_CompileGoInv_390 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'8804'_416 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.input-eq
d_input'45'eq_418 ::
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'eq_418 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.output-eq
d_output'45'eq_420 ::
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'eq_420 = erased
-- Once.Arith.Machine.CompileCorrect.run-abstract-app
d_run'45'abstract'45'app_432 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'abstract'45'app_432 = erased
-- Once.Arith.Machine.CompileCorrect.eval-arith-W-ainput
d_eval'45'arith'45'W'45'ainput_452 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'ainput_452 = erased
-- Once.Arith.Machine.CompileCorrect.eval-arith-W-finput
d_eval'45'arith'45'W'45'finput_470 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'finput_470 = erased
-- Once.Arith.Machine.CompileCorrect.compile-go-correct-ainput
d_compile'45'go'45'correct'45'ainput_490 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_compile'45'go'45'correct'45'ainput_490 = erased
-- Once.Arith.Machine.CompileCorrect.d≢i
d_d'8802'i_508 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8802'i_508 = erased
-- Once.Arith.Machine.CompileCorrect.<-suc
d_'60''45'suc_518 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'suc_518 ~v0 ~v1 ~v2 ~v3 v4 = du_'60''45'suc_518 v4
du_'60''45'suc_518 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'suc_518 v0 = coe v0
-- Once.Arith.Machine.CompileCorrect.compile-go-correct
d_compile'45'go'45'correct_532 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_compile'45'go'45'correct_532 = erased
-- Once.Arith.Machine.CompileCorrect.aneg-correct
d_aneg'45'correct_542 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_aneg'45'correct_542 = erased
-- Once.Arith.Machine.CompileCorrect._.ih
d_ih_556 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih_556 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_558 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_558 = erased
-- Once.Arith.Machine.CompileCorrect.aadd-correct
d_aadd'45'correct_578 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_aadd'45'correct_578 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_594 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_594 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_596 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_596 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_596 v0 v1 v2 v3 v4 v6
du_s1_596 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_596 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_598 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_598 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_598 v0 v1 v2 v3 v4 v6
du_s2_598 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_598 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_596 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_600 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_600 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_602 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_602 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_598 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_604 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_604 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_602
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_606 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_606 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_604
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_608 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_608 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_610 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_610 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_612 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_612 = erased
-- Once.Arith.Machine.CompileCorrect.asub-correct
d_asub'45'correct_634 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_asub'45'correct_634 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_650 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_650 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_652 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_652 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_652 v0 v1 v2 v3 v4 v6
du_s1_652 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_652 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_654 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_654 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_654 v0 v1 v2 v3 v4 v6
du_s2_654 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_654 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_652 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_656 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_656 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_658 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_658 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_660 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_660 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_658
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_662 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_662 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_660
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_664 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_664 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_666 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_666 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_668 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_668 = erased
-- Once.Arith.Machine.CompileCorrect.amul-correct
d_amul'45'correct_690 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_amul'45'correct_690 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_706 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_706 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_708 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_708 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_708 v0 v1 v2 v3 v4 v6
du_s1_708 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_708 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_710 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_710 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_710 v0 v1 v2 v3 v4 v6
du_s2_710 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_710 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_708 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_712 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_712 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_714 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_714 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_710 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_716 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_716 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_714
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_718 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_718 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_716
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_720 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_720 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_724 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_724 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_726 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_726 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_728 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_728 = erased
-- Once.Arith.Machine.CompileCorrect.adiv-correct
d_adiv'45'correct_748 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_adiv'45'correct_748 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_764 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_764 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_766 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_766 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_766 v0 v1 v2 v3 v4 v6
du_s1_766 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_766 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_768 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_768 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_768 v0 v1 v2 v3 v4 v6
du_s2_768 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_768 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_766 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_770 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_770 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_772 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_772 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_768 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_774 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_774 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_772
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_776 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_776 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_774
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_778 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_778 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_782 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_782 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_784 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_784 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_786 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_786 = erased
-- Once.Arith.Machine.CompileCorrect.amod-correct
d_amod'45'correct_806 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_amod'45'correct_806 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_822 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_822 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_824 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_824 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_824 v0 v1 v2 v3 v4 v6
du_s1_824 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_824 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_826 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_826 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_826 v0 v1 v2 v3 v4 v6
du_s2_826 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_826 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_828 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_828 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_830 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_830 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_826 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_832 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_832 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_830
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_834 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_834 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_832
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_836 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_836 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_838 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_838 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_840 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_840 = erased
-- Once.Arith.Machine.CompileCorrect.fneg-correct
d_fneg'45'correct_860 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_fneg'45'correct_860 = erased
-- Once.Arith.Machine.CompileCorrect._.ih
d_ih_874 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih_874 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_876 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_876 = erased
-- Once.Arith.Machine.CompileCorrect.i2f-correct
d_i2f'45'correct_894 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_i2f'45'correct_894 = erased
-- Once.Arith.Machine.CompileCorrect._.ih
d_ih_908 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih_908 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_910 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_910 = erased
-- Once.Arith.Machine.CompileCorrect.fadd-correct
d_fadd'45'correct_932 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_fadd'45'correct_932 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_948 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_948 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_950 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_950 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_950 v0 v1 v2 v3 v4 v6
du_s1_950 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_950 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_952 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_952 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_952 v0 v1 v2 v3 v4 v6
du_s2_952 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_952 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_950 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_954 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_954 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_956 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_956 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_952 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_958 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_958 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_956
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_960 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_960 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_958
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_962 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_962 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_964 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_964 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_966 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_966 = erased
-- Once.Arith.Machine.CompileCorrect.fsub-correct
d_fsub'45'correct_988 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_fsub'45'correct_988 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_1004 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_1004 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1006 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1006 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_1006 v0 v1 v2 v3 v4 v6
du_s1_1006 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1006 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1008 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1008 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_1008 v0 v1 v2 v3 v4 v6
du_s2_1008 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1008 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1006 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1010 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_1010 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1012 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1012 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1008 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1014 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1014 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_1012
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1016 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1016 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_1014
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1018 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1018 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1020 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1020 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1022 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1022 = erased
-- Once.Arith.Machine.CompileCorrect.fmul-correct
d_fmul'45'correct_1044 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_fmul'45'correct_1044 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_1060 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_1060 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1062 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1062 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_1062 v0 v1 v2 v3 v4 v6
du_s1_1062 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1062 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1064 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1064 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_1064 v0 v1 v2 v3 v4 v6
du_s2_1064 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1064 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1062 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1066 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_1066 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1068 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1068 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1064 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1070 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1070 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_1068
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1072 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1072 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_1070
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1074 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1074 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1076 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1076 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1078 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1078 = erased
-- Once.Arith.Machine.CompileCorrect.fdiv-correct
d_fdiv'45'correct_1100 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_fdiv'45'correct_1100 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_1116 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'a_1116 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1118 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1118 v0 v1 v2 v3 v4 ~v5 v6 = du_s1_1118 v0 v1 v2 v3 v4 v6
du_s1_1118 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1118 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1120 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1120 v0 v1 v2 v3 v4 ~v5 v6 = du_s2_1120 v0 v1 v2 v3 v4 v6
du_s2_1120 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1120 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1118 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1122 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_ih'45'b_1122 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1124 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1124 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1126 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1126 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (d_s3_1124
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1128 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1128 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_50
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_1126
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1130 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1130 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1132 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1132 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1134 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1134 = erased
-- Once.Arith.Machine.CompileCorrect.abs-validity
d_abs'45'validity_1282 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_1282 = erased
-- Once.Arith.Machine.CompileCorrect._.eval-in-range
d_eval'45'in'45'range_1304 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eval'45'in'45'range_1304 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_eval'45'in'45'range_1304 v0 v1 v4 v5 v6
du_eval'45'in'45'range_1304 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eval'45'in'45'range_1304 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v5
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174 (coe v0) (coe v5)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v6
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.du_readLeaf_96 (coe v2)
                (coe v6) (coe v4))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v4)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4))
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
                   (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                      (coe v0) (coe v1) (coe v2)
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v4))))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                mulInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v4)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v6 v7
        -> coe
             MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v4))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v5 v6
        -> coe
             MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v5) (coe v4))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4))
             (coe
                du_eval'45'in'45'range_1304 (coe v0) (coe v1) (coe v2) (coe v5)
                (coe v4))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v6
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
                (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v4)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.CompileCorrect._.fold-div-preserves
d_fold'45'div'45'preserves_1356 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'div'45'preserves_1356 = erased
-- Once.Arith.Machine.CompileCorrect._.fold-mod-preserves
d_fold'45'mod'45'preserves_1416 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'mod'45'preserves_1416 = erased
-- Once.Arith.Machine.CompileCorrect._.normalize-preserves
d_normalize'45'preserves_1472 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'preserves_1472 = erased
