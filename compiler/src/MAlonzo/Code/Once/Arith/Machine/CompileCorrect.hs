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
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.CompileCorrect._.run-abstract
d_run'45'abstract_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_14 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1)
-- Once.Arith.Machine.CompileCorrect._.step
d_step_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_16 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 (coe v0)
      (coe v1)
-- Once.Arith.Machine.CompileCorrect._._/ˢ_
d__'47''738'__22 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d__'47''738'__22 v0 ~v1 = du__'47''738'__22 v0
du__'47''738'__22 :: Integer -> Integer -> Integer -> Integer
du__'47''738'__22 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'47''738'__116 (coe v0)
-- Once.Arith.Machine.CompileCorrect._._⊗_
d__'8855'__28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d__'8855'__28 v0 ~v1 = du__'8855'__28 v0
du__'8855'__28 :: Integer -> Integer -> Integer -> Integer
du__'8855'__28 v0
  = coe MAlonzo.Code.Once.Spec.Word.d__'8855'__40 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.fromℤ
d_fromℤ_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer
d_fromℤ_30 v0 ~v1 = du_fromℤ_30 v0
du_fromℤ_30 :: Integer -> Integer -> Integer
du_fromℤ_30 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.modulus
d_modulus_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 -> Integer
d_modulus_32 v0 ~v1 = du_modulus_32 v0
du_modulus_32 :: Integer -> Integer
du_modulus_32 v0
  = coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.sdiv2ᵏ
d_sdiv2'7503'_62 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_62 v0 ~v1 = du_sdiv2'7503'_62 v0
du_sdiv2'7503'_62 :: Integer -> Integer -> Integer -> Integer
du_sdiv2'7503'_62 v0
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_70 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.shlᵂ
d_shl'7490'_64 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer
d_shl'7490'_64 v0 ~v1 = du_shl'7490'_64 v0
du_shl'7490'_64 :: Integer -> Integer -> Integer -> Integer
du_shl'7490'_64 v0
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_64 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.eval-arith-W
d_eval'45'arith'45'W_70 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_70 v0 v1
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
      (coe v0) (coe v1)
-- Once.Arith.Machine.CompileCorrect.step-div-safe≡
d_step'45'div'45'safe'8801'_76 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'safe'8801'_76 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-instr
d_step'45'div'45'instr_86 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'instr_86 = erased
-- Once.Arith.Machine.CompileCorrect.step-mul-op-eq
d_step'45'mul'45'op'45'eq_100 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mul'45'op'45'eq_100 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_130 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_132 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_138 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-op-eq
d_step'45'div'45'op'45'eq_246 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'op'45'eq_246 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_276 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_276 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_278 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_278 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_284 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_284 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-instr
d_step'45'rem'45'instr_390 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'instr_390 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-op
d_step'45'rem'45'op_402 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'op_402 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv
d_CompileGoInv_418 a0 a1 a2 a3 a4 a5 a6 = ()
data T_CompileGoInv_418 = C_constructor_450
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.reg0
d_reg0_440 ::
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg0_440 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.scratch≤
d_scratch'8804'_444 ::
  T_CompileGoInv_418 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'8804'_444 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.input-eq
d_input'45'eq_446 ::
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'eq_446 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.output-eq
d_output'45'eq_448 ::
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'eq_448 = erased
-- Once.Arith.Machine.CompileCorrect.run-abstract-app
d_run'45'abstract'45'app_460 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'abstract'45'app_460 = erased
-- Once.Arith.Machine.CompileCorrect.eval-arith-W-ainput
d_eval'45'arith'45'W'45'ainput_480 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'ainput_480 = erased
-- Once.Arith.Machine.CompileCorrect.eval-arith-W-finput
d_eval'45'arith'45'W'45'finput_498 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'finput_498 = erased
-- Once.Arith.Machine.CompileCorrect.compile-go-correct-ainput
d_compile'45'go'45'correct'45'ainput_518 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418
d_compile'45'go'45'correct'45'ainput_518 = erased
-- Once.Arith.Machine.CompileCorrect.d≢i
d_d'8802'i_536 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8802'i_536 = erased
-- Once.Arith.Machine.CompileCorrect.<-suc
d_'60''45'suc_546 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'suc_546 ~v0 ~v1 ~v2 ~v3 v4 = du_'60''45'suc_546 v4
du_'60''45'suc_546 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'suc_546 v0 = coe v0
-- Once.Arith.Machine.CompileCorrect.aneg-correct
d_aneg'45'correct_558 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 -> T_CompileGoInv_418
d_aneg'45'correct_558 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_574 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_574 = erased
-- Once.Arith.Machine.CompileCorrect.aadd-correct
d_aadd'45'correct_596 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_aadd'45'correct_596 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_616 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_616 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_616 v0 v1 v2 v3 v4 v6
du_s1_616 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_616 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_618 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_618 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_618 v0 v1 v2 v3 v4 v6
du_s2_618 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_618 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_616 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_620 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_620 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_622 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_622 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_622 v0 v1 v2 v3 v4 v5 v6
du_s3_622 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_622 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_618 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_624 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_624 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_624 v0 v1 v2 v3 v4 v5 v6
du_s4_624 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_624 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_622 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_626 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_626 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_626 v0 v1 v2 v3 v4 v5 v6
du_s5_626 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_626 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_624 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_628 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_628 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_630 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_630 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_632 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_632 = erased
-- Once.Arith.Machine.CompileCorrect.asub-correct
d_asub'45'correct_656 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_asub'45'correct_656 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_676 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_676 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_676 v0 v1 v2 v3 v4 v6
du_s1_676 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_676 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_678 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_678 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_678 v0 v1 v2 v3 v4 v6
du_s2_678 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_678 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_676 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_680 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_680 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_682 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_682 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_682 v0 v1 v2 v3 v4 v5 v6
du_s3_682 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_682 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_684 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_684 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_684 v0 v1 v2 v3 v4 v5 v6
du_s4_684 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_684 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_682 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_686 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_686 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_686 v0 v1 v2 v3 v4 v5 v6
du_s5_686 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_686 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_684 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_688 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_688 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_690 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_690 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_692 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_692 = erased
-- Once.Arith.Machine.CompileCorrect.acmp-correct
d_acmp'45'correct_718 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_acmp'45'correct_718 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_740 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_740 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_s1_740 v0 v1 v2 v4 v5 v7
du_s1_740 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_740 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_742 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_742 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_s2_742 v0 v1 v2 v4 v5 v7
du_s2_742 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_742 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_740 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_744 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_744 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_746 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_746 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9
  = du_s3_746 v0 v1 v2 v4 v5 v6 v7
du_s3_746 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_746 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_742 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_748 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_748 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9
  = du_s4_748 v0 v1 v2 v4 v5 v6 v7
du_s4_748 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_748 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_746 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_750 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_750 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_s5_750 v0 v1 v2 v3 v4 v5 v6 v7
du_s5_750 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_750 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_cmp'45'rrr_24 (coe v3)
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_748 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
         (coe v7))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_752 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_752 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_754 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_754 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_756 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_756 = erased
-- Once.Arith.Machine.CompileCorrect.amul-correct
d_amul'45'correct_780 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_amul'45'correct_780 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_800 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_800 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_800 v0 v1 v2 v3 v4 v6
du_s1_800 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_800 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_802 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_802 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_802 v0 v1 v2 v3 v4 v6
du_s2_802 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_802 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_800 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_804 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_804 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_806 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_806 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_806 v0 v1 v2 v3 v4 v5 v6
du_s3_806 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_806 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_802 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_808 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_808 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_808 v0 v1 v2 v3 v4 v5 v6
du_s4_808 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_808 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_810 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_810 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_810 v0 v1 v2 v3 v4 v5 v6
du_s5_810 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_810 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_812 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_812 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_816 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_816 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_818 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_818 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_820 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_820 = erased
-- Once.Arith.Machine.CompileCorrect.adiv-correct
d_adiv'45'correct_842 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_adiv'45'correct_842 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_862 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_862 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_862 v0 v1 v2 v3 v4 v6
du_s1_862 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_862 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_864 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_864 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_864 v0 v1 v2 v3 v4 v6
du_s2_864 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_864 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_866 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_866 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_868 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_868 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_868 v0 v1 v2 v3 v4 v5 v6
du_s3_868 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_868 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_864 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_870 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_870 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_870 v0 v1 v2 v3 v4 v5 v6
du_s4_870 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_870 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_868 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_872 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_872 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_872 v0 v1 v2 v3 v4 v5 v6
du_s5_872 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_872 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_870 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_874 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_874 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_878 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_878 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_880 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_880 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_882 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_882 = erased
-- Once.Arith.Machine.CompileCorrect.amod-correct
d_amod'45'correct_904 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_amod'45'correct_904 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_924 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_924 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_924 v0 v1 v2 v3 v4 v6
du_s1_924 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_924 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_926 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_926 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_926 v0 v1 v2 v3 v4 v6
du_s2_926 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_926 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_924 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_928 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_928 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_930 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_930 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_930 v0 v1 v2 v3 v4 v5 v6
du_s3_930 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_930 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_926 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_932 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_932 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_932 v0 v1 v2 v3 v4 v5 v6
du_s4_932 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_932 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_930 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_934 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_934 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_934 v0 v1 v2 v3 v4 v5 v6
du_s5_934 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_934 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_932 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_936 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_936 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_938 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_938 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_940 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_940 = erased
-- Once.Arith.Machine.CompileCorrect.fneg-correct
d_fneg'45'correct_960 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 -> T_CompileGoInv_418
d_fneg'45'correct_960 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_976 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_976 = erased
-- Once.Arith.Machine.CompileCorrect.i2f-correct
d_i2f'45'correct_994 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 -> T_CompileGoInv_418
d_i2f'45'correct_994 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1010 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1010 = erased
-- Once.Arith.Machine.CompileCorrect.fadd-correct
d_fadd'45'correct_1034 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_fadd'45'correct_1034 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1054 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1054 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1054 v0 v1 v2 v3 v4 v6
du_s1_1054 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1054 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1056 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1056 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1056 v0 v1 v2 v3 v4 v6
du_s2_1056 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1056 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1054 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1058 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_1058 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1060 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1060 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1060 v0 v1 v2 v3 v4 v5 v6
du_s3_1060 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1060 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1056 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1062 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1062 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1062 v0 v1 v2 v3 v4 v5 v6
du_s4_1062 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1062 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1060 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1064 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1064 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1064 v0 v1 v2 v3 v4 v5 v6
du_s5_1064 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1064 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_46
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1062 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1066 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1066 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1068 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1068 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1070 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1070 = erased
-- Once.Arith.Machine.CompileCorrect.fsub-correct
d_fsub'45'correct_1094 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_fsub'45'correct_1094 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1114 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1114 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1114 v0 v1 v2 v3 v4 v6
du_s1_1114 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1114 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1116 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1116 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1116 v0 v1 v2 v3 v4 v6
du_s2_1116 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1116 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1118 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_1118 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1120 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1120 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1120 v0 v1 v2 v3 v4 v5 v6
du_s3_1120 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1120 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1122 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1122 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1122 v0 v1 v2 v3 v4 v5 v6
du_s4_1122 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1122 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1124 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1124 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1124 v0 v1 v2 v3 v4 v5 v6
du_s5_1124 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1124 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_48
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1122 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1126 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1126 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1128 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1128 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1130 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1130 = erased
-- Once.Arith.Machine.CompileCorrect.fmul-correct
d_fmul'45'correct_1154 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_fmul'45'correct_1154 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1174 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1174 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1174 v0 v1 v2 v3 v4 v6
du_s1_1174 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1174 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1176 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1176 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1176 v0 v1 v2 v3 v4 v6
du_s2_1176 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1176 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1174 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1178 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_1178 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1180 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1180 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1180 v0 v1 v2 v3 v4 v5 v6
du_s3_1180 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1180 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1176 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1182 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1182 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1182 v0 v1 v2 v3 v4 v5 v6
du_s4_1182 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1182 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1180 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1184 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1184 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1184 v0 v1 v2 v3 v4 v5 v6
du_s5_1184 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1184 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_50
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1182 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1186 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1186 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1188 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1188 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1190 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1190 = erased
-- Once.Arith.Machine.CompileCorrect.fdiv-correct
d_fdiv'45'correct_1214 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_fdiv'45'correct_1214 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_1234 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_1234 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s1_1234 v0 v1 v2 v3 v4 v6
du_s1_1234 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_1234 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v3)
         (coe v4))
      (coe v5)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_1236 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_1236 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_s2_1236 v0 v1 v2 v3 v4 v6
du_s2_1236 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_1236 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_36
         (coe (0 :: Integer)) (coe v3))
      (coe
         du_s1_1234 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_1238 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  T_CompileGoInv_418
d_ih'45'b_1238 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_1240 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_1240 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s3_1240 v0 v1 v2 v3 v4 v5 v6
du_s3_1240 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s3_1240 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_298
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.d_compile'45'go_184
         (coe v2) (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))
      (coe
         du_s2_1236 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_1242 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_1242 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s4_1242 v0 v1 v2 v3 v4 v5 v6
du_s4_1242 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s4_1242 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_38 (coe v3)
         (coe (1 :: Integer)))
      (coe
         du_s3_1240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_1244 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_1244 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_s5_1244 v0 v1 v2 v3 v4 v5 v6
du_s5_1244 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s5_1244 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_112 v0 v1 v2
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_52
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (coe
         du_s4_1242 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_1246 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_1246 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_1248 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_1248 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_1250 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418 ->
  (MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
   T_CompileGoInv_418) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_1250 = erased
-- Once.Arith.Machine.CompileCorrect.compile-go-correct
d_compile'45'go'45'correct_1272 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_418
d_compile'45'go'45'correct_1272 = erased
-- Once.Arith.Machine.CompileCorrect.abs-validity
d_abs'45'validity_1440 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_1440 = erased
-- Once.Arith.Machine.CompileCorrect._.eval-in-range
d_eval'45'in'45'range_1462 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eval'45'in'45'range_1462 v0 v1 v2 ~v3 v4 v5 v6
  = du_eval'45'in'45'range_1462 v0 v1 v2 v4 v5 v6
du_eval'45'in'45'range_1462 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eval'45'in'45'range_1462 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v6
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106 (coe v0) (coe v6)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v7
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.du_readLeaf_96 (coe v3)
                (coe v7) (coe v5))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v8) (coe v5)))
             (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
                   (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                      (coe v0) (coe v1) (coe v3)
                      (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v8) (coe v5))))
             (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v7 v8
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                mulInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v8) (coe v5)))
             (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v7 v8
        -> coe
             MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v8) (coe v5))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v6 v7
        -> coe
             MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_530 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v5))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
             (coe
                du_eval'45'in'45'range_1462 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v6) (coe v5))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v7
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
                (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5)))
             (coe MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_acmp_46 v6 v7 v8
        -> coe
             du_bit'60'modulus_1524 (coe v2)
             (coe
                MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'word_22 (coe v0) (coe v6)
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
                   (coe v0) (coe v1) (coe v3)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v8) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.CompileCorrect._._.1<modulus
d_1'60'modulus_1518 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_1518 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_1'60'modulus_1518 v2
du_1'60'modulus_1518 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'60'modulus_1518 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
      (2 :: Integer) (1 :: Integer)
      (MAlonzo.Code.Data.Nat.Base.d__'94'__276
         (coe (2 :: Integer)) (coe v0))
      (coe MAlonzo.Code.Data.Nat.Properties.du_m'94'n'62'0_4482)
-- Once.Arith.Machine.CompileCorrect._._.bit<modulus
d_bit'60'modulus_1524 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Bool -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bit'60'modulus_1524 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_bit'60'modulus_1524 v2 v9
du_bit'60'modulus_1524 ::
  Integer -> Bool -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bit'60'modulus_1524 v0 v1
  = if coe v1
      then coe du_1'60'modulus_1518 (coe v0)
      else coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.Arith.Machine.CompileCorrect._.fold-div-preserves
d_fold'45'div'45'preserves_1534 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'div'45'preserves_1534 = erased
-- Once.Arith.Machine.CompileCorrect._.fold-mod-preserves
d_fold'45'mod'45'preserves_1598 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'mod'45'preserves_1598 = erased
-- Once.Arith.Machine.CompileCorrect._.normalize-preserves
d_normalize'45'preserves_1658 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'preserves_1658 = erased
