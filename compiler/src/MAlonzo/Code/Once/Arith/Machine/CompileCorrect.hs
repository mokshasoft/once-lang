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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
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
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.CompileCorrect._.run-abstract
d_run'45'abstract_12 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_run'45'abstract_12 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0)
-- Once.Arith.Machine.CompileCorrect._.step
d_step_14 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_step_14 v0
  = coe MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 (coe v0)
-- Once.Arith.Machine.CompileCorrect._._/ˢ_
d__'47''738'__20 :: Integer -> Integer -> Integer -> Integer
d__'47''738'__20 v0
  = coe MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0)
-- Once.Arith.Machine.CompileCorrect._._⊗_
d__'8855'__26 :: Integer -> Integer -> Integer -> Integer
d__'8855'__26 v0
  = coe MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.fromℤ
d_fromℤ_40 :: Integer -> Integer -> Integer
d_fromℤ_40 v0 = coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.modulus
d_modulus_48 :: Integer -> Integer
d_modulus_48 v0 = coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.sdiv2ᵏ
d_sdiv2'7503'_52 :: Integer -> Integer -> Integer -> Integer
d_sdiv2'7503'_52 v0
  = coe MAlonzo.Code.Once.Word.d_sdiv2'7503'_138 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.shlᵂ
d_shl'7490'_54 :: Integer -> Integer -> Integer -> Integer
d_shl'7490'_54 v0
  = coe MAlonzo.Code.Once.Word.d_shl'7490'_132 (coe v0)
-- Once.Arith.Machine.CompileCorrect._.eval-arith-W
d_eval'45'arith'45'W_62 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_62 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
      (coe v0)
-- Once.Arith.Machine.CompileCorrect.step-div-safe≡
d_step'45'div'45'safe'8801'_68 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'safe'8801'_68 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-instr
d_step'45'div'45'instr_78 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'instr_78 = erased
-- Once.Arith.Machine.CompileCorrect.step-mul-op-eq
d_step'45'mul'45'op'45'eq_92 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'mul'45'op'45'eq_92 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_122 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_124 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_130 = erased
-- Once.Arith.Machine.CompileCorrect.step-div-op-eq
d_step'45'div'45'op'45'eq_226 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'div'45'op'45'eq_226 = erased
-- Once.Arith.Machine.CompileCorrect._.k≡
d_k'8801'_256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_k'8801'_256 = erased
-- Once.Arith.Machine.CompileCorrect._.r0
d_r0_258 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r0_258 = erased
-- Once.Arith.Machine.CompileCorrect._.inner
d_inner_264 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_264 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-instr
d_step'45'rem'45'instr_358 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Bool ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'instr_358 = erased
-- Once.Arith.Machine.CompileCorrect.step-rem-op
d_step'45'rem'45'op_370 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'rem'45'op_370 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv
d_CompileGoInv_384 a0 a1 a2 a3 a4 = ()
data T_CompileGoInv_384 = C_constructor_414
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.reg0
d_reg0_404 ::
  T_CompileGoInv_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg0_404 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.scratch≤
d_scratch'8804'_408 ::
  T_CompileGoInv_384 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'8804'_408 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.input-eq
d_input'45'eq_410 ::
  T_CompileGoInv_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'eq_410 = erased
-- Once.Arith.Machine.CompileCorrect.CompileGoInv.output-eq
d_output'45'eq_412 ::
  T_CompileGoInv_384 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_output'45'eq_412 = erased
-- Once.Arith.Machine.CompileCorrect.run-abstract-app
d_run'45'abstract'45'app_424 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'abstract'45'app_424 = erased
-- Once.Arith.Machine.CompileCorrect.eval-arith-W-ainput
d_eval'45'arith'45'W'45'ainput_444 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'arith'45'W'45'ainput_444 = erased
-- Once.Arith.Machine.CompileCorrect.compile-go-correct-ainput
d_compile'45'go'45'correct'45'ainput_476 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_22] ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_compile'45'go'45'correct'45'ainput_476 = erased
-- Once.Arith.Machine.CompileCorrect.d≢i
d_d'8802'i_494 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8802'i_494 = erased
-- Once.Arith.Machine.CompileCorrect.<-suc
d_'60''45'suc_504 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'suc_504 ~v0 ~v1 ~v2 v3 = du_'60''45'suc_504 v3
du_'60''45'suc_504 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'suc_504 v0 = coe v0
-- Once.Arith.Machine.CompileCorrect.compile-go-correct
d_compile'45'go'45'correct_516 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_compile'45'go'45'correct_516 = erased
-- Once.Arith.Machine.CompileCorrect.aneg-correct
d_aneg'45'correct_526 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_aneg'45'correct_526 = erased
-- Once.Arith.Machine.CompileCorrect._.ih
d_ih_540 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih_540 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_542 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_542 = erased
-- Once.Arith.Machine.CompileCorrect.aadd-correct
d_aadd'45'correct_562 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_aadd'45'correct_562 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_578 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'a_578 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_580 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_580 v0 v1 v2 v3 ~v4 v5 = du_s1_580 v0 v1 v2 v3 v5
du_s1_580 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_580 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe v2) (coe v3))
      (coe v4)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_582 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_582 v0 v1 v2 v3 ~v4 v5 = du_s2_582 v0 v1 v2 v3 v5
du_s2_582 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_582 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v2))
      (coe du_s1_580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_584 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'b_584 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_586 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_586 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4))
      (coe du_s2_582 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_588 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_588 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
         (coe (1 :: Integer)))
      (d_s3_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_590 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_590 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_588 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_592 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_592 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_594 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_594 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_596 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_596 = erased
-- Once.Arith.Machine.CompileCorrect.asub-correct
d_asub'45'correct_618 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_asub'45'correct_618 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_634 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'a_634 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_636 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_636 v0 v1 v2 v3 ~v4 v5 = du_s1_636 v0 v1 v2 v3 v5
du_s1_636 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_636 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe v2) (coe v3))
      (coe v4)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_638 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_638 v0 v1 v2 v3 ~v4 v5 = du_s2_638 v0 v1 v2 v3 v5
du_s2_638 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_638 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v2))
      (coe du_s1_636 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_640 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'b_640 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_642 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_642 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4))
      (coe du_s2_638 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_644 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_644 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
         (coe (1 :: Integer)))
      (d_s3_642 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_646 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_646 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_644 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_648 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_648 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_650 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_650 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_652 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_652 = erased
-- Once.Arith.Machine.CompileCorrect.amul-correct
d_amul'45'correct_674 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_amul'45'correct_674 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_690 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'a_690 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_692 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_692 v0 v1 v2 v3 ~v4 v5 = du_s1_692 v0 v1 v2 v3 v5
du_s1_692 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_692 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe v2) (coe v3))
      (coe v4)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_694 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_694 v0 v1 v2 v3 ~v4 v5 = du_s2_694 v0 v1 v2 v3 v5
du_s2_694 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_694 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v2))
      (coe du_s1_692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_696 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'b_696 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_698 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_698 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4))
      (coe du_s2_694 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_700 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_700 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
         (coe (1 :: Integer)))
      (d_s3_698 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_702 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_702 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_700 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_704 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_704 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_708 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_708 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_710 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_710 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_712 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_712 = erased
-- Once.Arith.Machine.CompileCorrect.adiv-correct
d_adiv'45'correct_732 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_adiv'45'correct_732 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_748 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'a_748 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_750 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_750 v0 v1 v2 v3 ~v4 v5 = du_s1_750 v0 v1 v2 v3 v5
du_s1_750 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_750 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe v2) (coe v3))
      (coe v4)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_752 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_752 v0 v1 v2 v3 ~v4 v5 = du_s2_752 v0 v1 v2 v3 v5
du_s2_752 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_752 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v2))
      (coe du_s1_750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_754 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'b_754 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_756 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_756 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4))
      (coe du_s2_752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_758 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_758 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
         (coe (1 :: Integer)))
      (d_s3_756 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_760 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_760 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_762 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_762 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s4-0
d_regs'45's4'45'0_766 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's4'45'0_766 = erased
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_768 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_768 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_770 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_770 = erased
-- Once.Arith.Machine.CompileCorrect.amod-correct
d_amod'45'correct_790 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_amod'45'correct_790 = erased
-- Once.Arith.Machine.CompileCorrect._.ih-a
d_ih'45'a_806 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'a_806 = erased
-- Once.Arith.Machine.CompileCorrect._.s1
d_s1_808 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s1_808 v0 v1 v2 v3 ~v4 v5 = du_s1_808 v0 v1 v2 v3 v5
du_s1_808 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s1_808 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe v2) (coe v3))
      (coe v4)
-- Once.Arith.Machine.CompileCorrect._.s2
d_s2_810 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s2_810 v0 v1 v2 v3 ~v4 v5 = du_s2_810 v0 v1 v2 v3 v5
du_s2_810 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
du_s2_810 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34
         (coe (0 :: Integer)) (coe v2))
      (coe du_s1_808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Arith.Machine.CompileCorrect._.ih-b
d_ih'45'b_812 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  T_CompileGoInv_384
d_ih'45'b_812 = erased
-- Once.Arith.Machine.CompileCorrect._.s3
d_s3_814 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s3_814 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_run'45'abstract_200
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Compile.du_compile'45'go_174
         (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v4))
      (coe du_s2_810 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s4
d_s4_816 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s4_816 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 (coe v2)
         (coe (1 :: Integer)))
      (d_s3_814 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.s5
d_s5_818 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130
d_s5_818 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.d_step_84 v0 v1
      (coe
         MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22
         (coe (0 :: Integer)) (coe (1 :: Integer)) (coe (0 :: Integer)))
      (d_s4_816 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Arith.Machine.CompileCorrect._.bridge
d_bridge_820 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_820 = erased
-- Once.Arith.Machine.CompileCorrect._.scratch-s3-d
d_scratch'45's3'45'd_822 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45's3'45'd_822 = erased
-- Once.Arith.Machine.CompileCorrect._.regs-s3-0
d_regs'45's3'45'0_824 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_ArithAbsState_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_regs'45's3'45'0_824 = erased
-- Once.Arith.Machine.CompileCorrect.abs-validity
d_abs'45'validity_906 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'validity_906 = erased
-- Once.Arith.Machine.CompileCorrect._.eval-in-range
d_eval'45'in'45'range_928 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eval'45'in'45'range_928 v0 ~v1 ~v2 v3 v4 v5
  = du_eval'45'in'45'range_928 v0 v3 v4 v5
du_eval'45'in'45'range_928 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eval'45'in'45'range_928 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v4
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174 (coe v0) (coe v4)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v4
        -> let v5
                 = MAlonzo.Code.Once.Arith.Machine.Shape.d_project_32
                     (coe v1) (coe v4) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174 (coe v0) (coe v6)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174 (coe v0)
                       (coe (0 :: Integer))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v4) (coe v3))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v5) (coe v3)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                addInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v4) (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
                   (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                      (coe v0) (coe v1) (coe v5) (coe v3))))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                mulInt
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v4) (coe v3))
                (coe
                   MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v5) (coe v3)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604 (coe v0)
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                (coe v0) (coe v1) (coe v4) (coe v3))
             (coe
                MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                (coe v0) (coe v1) (coe v5) (coe v3))
             (coe
                du_eval'45'in'45'range_928 (coe v0) (coe v1) (coe v4) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v4
        -> coe
             MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
                (MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_32
                   (coe v0) (coe v1) (coe v4) (coe v3)))
             (coe MAlonzo.Code.Once.Word.d_modulus_10 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.CompileCorrect._.fold-div-preserves
d_fold'45'div'45'preserves_994 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'div'45'preserves_994 = erased
-- Once.Arith.Machine.CompileCorrect._.fold-mod-preserves
d_fold'45'mod'45'preserves_1054 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'mod'45'preserves_1054 = erased
-- Once.Arith.Machine.CompileCorrect._.normalize-preserves
d_normalize'45'preserves_1110 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'preserves_1110 = erased
