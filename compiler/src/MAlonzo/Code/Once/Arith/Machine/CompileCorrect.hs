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
-- Once.Arith.Machine.CompileCorrect.aneg-correct
d_aneg'45'correct_530 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 -> T_CompileGoInv_390
d_aneg'45'correct_530 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_546 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_546 = erased
-- Once.Arith.Machine.CompileCorrect.aadd-correct
d_aadd'45'correct_568 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_aadd'45'correct_568 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_588 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_588 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_588 v0 v1 v2 v3 v4 v6
du_s1_588 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_588 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_590 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_590 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_590 v0 v1 v2 v3 v4 v6
du_s2_590 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_590 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_588 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_592 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_592 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_594 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_594 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_594 v0 v1 v2 v3 v4 v5 v6
du_s3_594 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_594 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_590 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_596 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_596 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_596 v0 v1 v2 v3 v4 v5 v6
du_s4_596 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_596 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_594 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_598 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_598 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_598 v0 v1 v2 v3 v4 v5 v6
du_s5_598 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_598 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_596 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_600 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_600 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_602 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_602 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_604 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_604 = erased
-- Once.Arith.Machine.CompileCorrect.asub-correct
d_asub'45'correct_628 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_asub'45'correct_628 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_648 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_648 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_648 v0 v1 v2 v3 v4 v6
du_s1_648 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_648 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_650 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_650 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_650 v0 v1 v2 v3 v4 v6
du_s2_650 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_650 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_648 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_652 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_652 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_654 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_654 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_654 v0 v1 v2 v3 v4 v5 v6
du_s3_654 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_654 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_650 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_656 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_656 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_656 v0 v1 v2 v3 v4 v5 v6
du_s4_656 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_656 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_658 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_658 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_658 v0 v1 v2 v3 v4 v5 v6
du_s5_658 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_658 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_656 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_660 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_660 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_662 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_662 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_664 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_664 = erased
-- Once.Arith.Machine.CompileCorrect.amul-correct
d_amul'45'correct_688 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_amul'45'correct_688 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_708 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_708 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_708 v0 v1 v2 v3 v4 v6
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_710 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_710 v0 v1 v2 v3 v4 v6
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_714 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_714 v0 v1 v2 v3 v4 v5 v6
du_s3_714 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_714 v0 v1 v2 v3 v4 v5 v6
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_716 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_716 v0 v1 v2 v3 v4 v5 v6
du_s4_716 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_716 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_718 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_718 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_718 v0 v1 v2 v3 v4 v5 v6
du_s5_718 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_718 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_716 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_720 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
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
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_728 = erased
-- Once.Arith.Machine.CompileCorrect.adiv-correct
d_adiv'45'correct_750 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_adiv'45'correct_750 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_770 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_770 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_770 v0 v1 v2 v3 v4 v6
du_s1_770 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_770 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_772 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_772 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_772 v0 v1 v2 v3 v4 v6
du_s2_772 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_772 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_770 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_774 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_774 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_776 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_776 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_776 v0 v1 v2 v3 v4 v5 v6
du_s3_776 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_776 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_772 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_778 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_778 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_778 v0 v1 v2 v3 v4 v5 v6
du_s4_778 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_778 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_776 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_780 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_780 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_780 v0 v1 v2 v3 v4 v5 v6
du_s5_780 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_780 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_782 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_782 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_786 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_786 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_788 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_788 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_790 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_790 = erased
-- Once.Arith.Machine.CompileCorrect.amod-correct
d_amod'45'correct_812 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_amod'45'correct_812 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_832 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_832 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_832 v0 v1 v2 v3 v4 v6
du_s1_832 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_832 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_834 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_834 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_834 v0 v1 v2 v3 v4 v6
du_s2_834 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_834 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_832 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_836 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_836 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_838 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_838 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_838 v0 v1 v2 v3 v4 v5 v6
du_s3_838 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_838 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_840 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_840 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_840 v0 v1 v2 v3 v4 v5 v6
du_s4_840 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_840 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_838 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_842 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_842 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_842 v0 v1 v2 v3 v4 v5 v6
du_s5_842 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_842 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_844 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_844 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_846 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_846 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_848 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_848 = erased
-- Once.Arith.Machine.CompileCorrect.fneg-correct
d_fneg'45'correct_868 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 -> T_CompileGoInv_390
d_fneg'45'correct_868 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_884 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_884 = erased
-- Once.Arith.Machine.CompileCorrect.i2f-correct
d_i2f'45'correct_902 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 -> T_CompileGoInv_390
d_i2f'45'correct_902 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_918 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_918 = erased
-- Once.Arith.Machine.CompileCorrect.fadd-correct
d_fadd'45'correct_942 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_fadd'45'correct_942 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_962 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_962 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_962 v0 v1 v2 v3 v4 v6
du_s1_962 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_962 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_964 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_964 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_964 v0 v1 v2 v3 v4 v6
du_s2_964 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_964 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_962 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_966 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_966 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_968 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_968 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_968 v0 v1 v2 v3 v4 v5 v6
du_s3_968 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_968 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_964 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_970 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_970 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_970 v0 v1 v2 v3 v4 v5 v6
du_s4_970 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_970 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_968 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_972 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_972 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_972 v0 v1 v2 v3 v4 v5 v6
du_s5_972 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_972 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_970 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_974 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_974 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_976 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_976 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_978 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_978 = erased
-- Once.Arith.Machine.CompileCorrect.fsub-correct
d_fsub'45'correct_1002 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_fsub'45'correct_1002 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1022 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1022 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1022 v0 v1 v2 v3 v4 v6
du_s1_1022 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1022 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1024 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1024 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1024 v0 v1 v2 v3 v4 v6
du_s2_1024 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1024 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1022 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1026 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_1026 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1028 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1028 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1028 v0 v1 v2 v3 v4 v5 v6
du_s3_1028 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1028 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1024 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1030 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1030 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1030 v0 v1 v2 v3 v4 v5 v6
du_s4_1030 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1030 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1028 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1032 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1032 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1032 v0 v1 v2 v3 v4 v5 v6
du_s5_1032 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1032 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1030 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1034 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1034 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1036 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1036 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1038 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1038 = erased
-- Once.Arith.Machine.CompileCorrect.fmul-correct
d_fmul'45'correct_1062 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_fmul'45'correct_1062 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1082 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1082 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1082 v0 v1 v2 v3 v4 v6
du_s1_1082 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1082 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1084 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1084 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1084 v0 v1 v2 v3 v4 v6
du_s2_1084 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1084 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1082 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1086 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_1086 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1088 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1088 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1088 v0 v1 v2 v3 v4 v5 v6
du_s3_1088 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1088 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1084 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1090 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1090 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1090 v0 v1 v2 v3 v4 v5 v6
du_s4_1090 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1090 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1088 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1092 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1092 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1092 v0 v1 v2 v3 v4 v5 v6
du_s5_1092 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1092 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1090 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1094 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1094 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1096 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1096 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1098 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1098 = erased
-- Once.Arith.Machine.CompileCorrect.fdiv-correct
d_fdiv'45'correct_1122 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_fdiv'45'correct_1122 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1142 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1142 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1142 v0 v1 v2 v3 v4 v6
du_s1_1142 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1142 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1144 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1144 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1144 v0 v1 v2 v3 v4 v6
du_s2_1144 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1144 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1142 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1146 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  T_CompileGoInv_390
d_ih'45'b_1146 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1148 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1148 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1148 v0 v1 v2 v3 v4 v5 v6
du_s3_1148 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1148 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_284
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_180
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1144 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1150 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1150 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1150 v0 v1 v2 v3 v4 v5 v6
du_s4_1150 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1150 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1148 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1152 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1152 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1152 v0 v1 v2 v3 v4 v5 v6
du_s5_1152 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1152 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_108 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_50
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1150 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1154 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1154 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1156 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1156 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1158 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_390) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1158 = erased
-- Once.Arith.Machine.CompileCorrect.compile-go-correct
d_compile'45'go'45'correct_1180 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_390
d_compile'45'go'45'correct_1180 = erased
-- Once.Arith.Machine.CompileCorrect.abs-validity
d_abs'45'validity_1336 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_1336 = erased
-- Once.Arith.Machine.CompileCorrect._.eval-in-range
d_eval'45'in'45'range_1358 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eval'45'in'45'range_1358 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_eval'45'in'45'range_1358 v0 v1 v4 v5 v6
du_eval'45'in'45'range_1358 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eval'45'in'45'range_1358 v0 v1 v2 v3 v4
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
                du_eval'45'in'45'range_1358 (coe v0) (coe v1) (coe v2) (coe v5)
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
d_fold'45'div'45'preserves_1410 ::
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
d_fold'45'div'45'preserves_1410 = erased
-- Once.Arith.Machine.CompileCorrect._.fold-mod-preserves
d_fold'45'mod'45'preserves_1470 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'mod'45'preserves_1470 = erased
-- Once.Arith.Machine.CompileCorrect._.normalize-preserves
d_normalize'45'preserves_1526 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'preserves_1526 = erased
