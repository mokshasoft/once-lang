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

module MAlonzo.Code.Once.Adequacy.LiftSound where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Recognise
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.LiftSound.M.⟦_⟧
d_'10214'_'10215'_118 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_118 = erased
-- Once.Adequacy.LiftSound.W._%ˢ_
d__'37''738'__136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'37''738'__136 ~v0 ~v1 v2 = du__'37''738'__136 v2
du__'37''738'__136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du__'37''738'__136 v0
  = coe
      MAlonzo.Code.Once.Word.d__'37''738'__126
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W._/ˢ_
d__'47''738'__138 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'47''738'__138 ~v0 ~v1 v2 = du__'47''738'__138 v2
du__'47''738'__138 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du__'47''738'__138 v0
  = coe
      MAlonzo.Code.Once.Word.d__'47''738'__120
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W._<ˢ_
d__'60''738'__140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'60''738'__140 ~v0 ~v1 v2 = du__'60''738'__140 v2
du__'60''738'__140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
du__'60''738'__140 v0
  = coe
      MAlonzo.Code.Once.Word.d__'60''738'__80
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W._≡ʷ_
d__'8801''695'__142 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Bool
d__'8801''695'__142 ~v0 ~v1 ~v2 = du__'8801''695'__142
du__'8801''695'__142 :: Integer -> Integer -> Bool
du__'8801''695'__142
  = coe MAlonzo.Code.Once.Word.du__'8801''695'__86
-- Once.Adequacy.LiftSound.W._⊕_
d__'8853'__144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8853'__144 ~v0 ~v1 v2 = du__'8853'__144 v2
du__'8853'__144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du__'8853'__144 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8853'__26
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W._⊖_
d__'8854'__146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8854'__146 ~v0 ~v1 v2 = du__'8854'__146 v2
du__'8854'__146 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du__'8854'__146 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8854'__32
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W._⊗_
d__'8855'__148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d__'8855'__148 ~v0 ~v1 v2 = du__'8855'__148 v2
du__'8855'__148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du__'8855'__148 v0
  = coe
      MAlonzo.Code.Once.Word.d__'8855'__38
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.%ˢ-else
d_'37''738''45'else_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_150 = erased
-- Once.Adequacy.LiftSound.W.%ˢ-in-range
d_'37''738''45'in'45'range_152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_152 ~v0 ~v1 v2
  = du_'37''738''45'in'45'range_152 v2
du_'37''738''45'in'45'range_152 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'37''738''45'in'45'range_152 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_604
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
      v5
-- Once.Adequacy.LiftSound.W.%ˢ-mid
d_'37''738''45'mid_154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_154 = erased
-- Once.Adequacy.LiftSound.W.%ˢ-negOne
d_'37''738''45'negOne_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_156 = erased
-- Once.Adequacy.LiftSound.W.%ˢ-zero
d_'37''738''45'zero_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_158 = erased
-- Once.Adequacy.LiftSound.W./ˢ-else
d_'47''738''45'else_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_160 = erased
-- Once.Adequacy.LiftSound.W./ˢ-in-range
d_'47''738''45'in'45'range_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_162 ~v0 ~v1 v2
  = du_'47''738''45'in'45'range_162 v2
du_'47''738''45'in'45'range_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''738''45'in'45'range_162 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_570
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Adequacy.LiftSound.W./ˢ-mid
d_'47''738''45'mid_164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_164 = erased
-- Once.Adequacy.LiftSound.W./ˢ-negOne
d_'47''738''45'negOne_166 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_166 = erased
-- Once.Adequacy.LiftSound.W./ˢ-pow2
d_'47''738''45'pow2_168 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_168 = erased
-- Once.Adequacy.LiftSound.W./ˢ-zero
d_'47''738''45'zero_170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_170 = erased
-- Once.Adequacy.LiftSound.W.0<half
d_0'60'half_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_172 ~v0 ~v1 ~v2 = du_0'60'half_172
du_0'60'half_172 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_172 = coe MAlonzo.Code.Once.Word.du_0'60'half_168
-- Once.Adequacy.LiftSound.W.0<modulus
d_0'60'modulus_174 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_174 ~v0 ~v1 ~v2 = du_0'60'modulus_174
du_0'60'modulus_174 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_174
  = coe MAlonzo.Code.Once.Word.du_0'60'modulus_166
-- Once.Adequacy.LiftSound.W.0<negOne
d_0'60'negOne_176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_176 ~v0 ~v1 v2 = du_0'60'negOne_176 v2
du_0'60'negOne_176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'negOne_176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_426
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.1<modulus
d_1'60'modulus_178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_178 ~v0 ~v1 v2 = du_1'60'modulus_178 v2
du_1'60'modulus_178 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'60'modulus_178 v0
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_796
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.2*n≡n+n
d_2'42'n'8801'n'43'n_180 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_180 = erased
-- Once.Adequacy.LiftSound.W.2≤modulus
d_2'8804'modulus_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_182 ~v0 ~v1 v2 = du_2'8804'modulus_182 v2
du_2'8804'modulus_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_2'8804'modulus_182 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_422
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.<⇒<ᵇtrue
d_'60''8658''60''7495'true_184 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_184 = erased
-- Once.Adequacy.LiftSound.W.InRange
d_InRange_186 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> ()
d_InRange_186 = erased
-- Once.Adequacy.LiftSound.W.Word
d_Word_188 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> ()
d_Word_188 = erased
-- Once.Adequacy.LiftSound.W.fromℤ
d_fromℤ_190 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_fromℤ_190 ~v0 ~v1 v2 = du_fromℤ_190 v2
du_fromℤ_190 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
du_fromℤ_190 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ_20
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.fromℤ-0
d_fromℤ'45'0_192 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_192 = erased
-- Once.Adequacy.LiftSound.W.fromℤ-in-range
d_fromℤ'45'in'45'range_194 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_194 ~v0 ~v1 v2
  = du_fromℤ'45'in'45'range_194 v2
du_fromℤ'45'in'45'range_194 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fromℤ'45'in'45'range_194 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_174
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_196 = erased
-- Once.Adequacy.LiftSound.W.fromℤ-neg1
d_fromℤ'45'neg1_198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_198 = erased
-- Once.Adequacy.LiftSound.W.half
d_half_200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_half_200 ~v0 ~v1 v2 = du_half_200 v2
du_half_200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
du_half_200 v0
  = coe
      MAlonzo.Code.Once.Word.d_half_48
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.half<modulus
d_half'60'modulus_202 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_202 ~v0 ~v1 v2 = du_half'60'modulus_202 v2
du_half'60'modulus_202 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'60'modulus_202 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_430
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.half≡2^b
d_half'8801'2'94'b_204 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_204 = erased
-- Once.Adequacy.LiftSound.W.half≤negOne
d_half'8804'negOne_206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_206 ~v0 ~v1 v2 = du_half'8804'negOne_206 v2
du_half'8804'negOne_206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_half'8804'negOne_206 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_450
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.inRange?
d_inRange'63'_208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_208 ~v0 ~v1 v2 = du_inRange'63'_208 v2
du_inRange'63'_208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inRange'63'_208 v0
  = coe
      MAlonzo.Code.Once.Word.d_inRange'63'_62
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.intMin
d_intMin_210 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_intMin_210 ~v0 ~v1 v2 = du_intMin_210 v2
du_intMin_210 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
du_intMin_210 v0
  = coe
      MAlonzo.Code.Once.Word.d_intMin_54
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.lit-hi
d_lit'45'hi_212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_212 ~v0 ~v1 ~v2 = du_lit'45'hi_212
du_lit'45'hi_212 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_212 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_654 v3
-- Once.Adequacy.LiftSound.W.lit-lo
d_lit'45'lo_214 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_214 ~v0 ~v1 v2 = du_lit'45'lo_214 v2
du_lit'45'lo_214 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'lo_214 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_666
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v3 v4
-- Once.Adequacy.LiftSound.W.modulus
d_modulus_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_modulus_216 ~v0 ~v1 v2 = du_modulus_216 v2
du_modulus_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
du_modulus_216 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus_10
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_218 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_218 = erased
-- Once.Adequacy.LiftSound.W.modulus≢0
d_modulus'8802'0_220 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_220 ~v0 ~v1 v2 = du_modulus'8802'0_220 v2
du_modulus'8802'0_220 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_modulus'8802'0_220 v0
  = coe
      MAlonzo.Code.Once.Word.d_modulus'8802'0_12
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.mod∸half≡half
d_mod'8760'half'8801'half_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_222 = erased
-- Once.Adequacy.LiftSound.W.mod≡half+half
d_mod'8801'half'43'half_224 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_224 = erased
-- Once.Adequacy.LiftSound.W.negOne
d_negOne_226 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
d_negOne_226 ~v0 ~v1 v2 = du_negOne_226 v2
du_negOne_226 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer
du_negOne_226 v0
  = coe
      MAlonzo.Code.Once.Word.d_negOne_78
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.negOne<modulus
d_negOne'60'modulus_228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_228 ~v0 ~v1 v2 = du_negOne'60'modulus_228 v2
du_negOne'60'modulus_228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_negOne'60'modulus_228 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_438
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.negOne≢0
d_negOne'8802'0_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_230 = erased
-- Once.Adequacy.LiftSound.W.norm
d_norm_232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_norm_232 ~v0 ~v1 v2 = du_norm_232 v2
du_norm_232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
du_norm_232 v0
  = coe
      MAlonzo.Code.Once.Word.d_norm_16
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.norm-0
d_norm'45'0_234 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_234 = erased
-- Once.Adequacy.LiftSound.W.norm-id
d_norm'45'id_236 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_236 = erased
-- Once.Adequacy.LiftSound.W.sbb-pos
d_sbb'45'pos_238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_238 = erased
-- Once.Adequacy.LiftSound.W.sbb-zero
d_sbb'45'zero_240 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_240 = erased
-- Once.Adequacy.LiftSound.W.sdiv2ᵏ
d_sdiv2'7503'_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_242 ~v0 ~v1 v2 = du_sdiv2'7503'_242 v2
du_sdiv2'7503'_242 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du_sdiv2'7503'_242 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_138
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.shlᵂ
d_shl'7490'_244 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
d_shl'7490'_244 ~v0 ~v1 v2 = du_shl'7490'_244 v2
du_shl'7490'_244 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Integer -> Integer
du_shl'7490'_244 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_132
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.sucNegOne≡mod
d_sucNegOne'8801'mod_246 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_246 = erased
-- Once.Adequacy.LiftSound.W.tdiv-neg1
d_tdiv'45'neg1_248 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_248 = erased
-- Once.Adequacy.LiftSound.W.tmod-neg1
d_tmod'45'neg1_250 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_250 = erased
-- Once.Adequacy.LiftSound.W.toWord
d_toWord_252 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_252 ~v0 ~v1 v2 = du_toWord_252 v2
du_toWord_252 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_toWord_252 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_toWord_68
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0)) v1
-- Once.Adequacy.LiftSound.W.toWord≡fromℤ
d_toWord'8801'fromℤ_254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_254 = erased
-- Once.Adequacy.LiftSound.W.toℤ
d_toℤ_256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_toℤ_256 ~v0 ~v1 v2 = du_toℤ_256 v2
du_toℤ_256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
du_toℤ_256 v0
  = coe
      MAlonzo.Code.Once.Word.d_toℤ_50
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.toℤ-negOne
d_toℤ'45'negOne_258 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_258 = erased
-- Once.Adequacy.LiftSound.W.toℤ∘fromℤ
d_toℤ'8728'fromℤ_260 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_260 = erased
-- Once.Adequacy.LiftSound.W.unplus
d_unplus_262 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_262 ~v0 ~v1 ~v2 = du_unplus_262
du_unplus_262 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_262 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_648 v4
-- Once.Adequacy.LiftSound.W.≡ᵇ-refl
d_'8801''7495''45'refl_264 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_264 = erased
-- Once.Adequacy.LiftSound.W.≡ᵇ0-false
d_'8801''7495'0'45'false_266 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_266 = erased
-- Once.Adequacy.LiftSound.W.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_268 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_268 = erased
-- Once.Adequacy.LiftSound.W.⊕-neg
d_'8853''45'neg_270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_270 = erased
-- Once.Adequacy.LiftSound.W.⊕-neg-suc
d_'8853''45'neg'45'suc_272 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_272 = erased
-- Once.Adequacy.LiftSound.W.⊕-normʳ
d_'8853''45'norm'691'_274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_274 = erased
-- Once.Adequacy.LiftSound.W.⊕≡+
d_'8853''8801''43'_276 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_276 = erased
-- Once.Adequacy.LiftSound.W.⊖-normʳ
d_'8854''45'norm'691'_278 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_278 = erased
-- Once.Adequacy.LiftSound.W.⊖-self
d_'8854''45'self_280 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_280 = erased
-- Once.Adequacy.LiftSound.W.⊖≡∸
d_'8854''8801''8760'_282 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_282 = erased
-- Once.Adequacy.LiftSound.W.⊗-pow2
d_'8855''45'pow2_284 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_284 = erased
-- Once.Adequacy.LiftSound.W.⊝_
d_'8861'__286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
d_'8861'__286 ~v0 ~v1 v2 = du_'8861'__286 v2
du_'8861'__286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> Integer -> Integer
du_'8861'__286 v0
  = coe
      MAlonzo.Code.Once.Word.d_'8861'__44
      (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
-- Once.Adequacy.LiftSound.W.⊝-fromℤ
d_'8861''45'fromℤ_288 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_288 = erased
-- Once.Adequacy.LiftSound.W.⊝-intMin
d_'8861''45'intMin_290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_290 = erased
-- Once.Adequacy.LiftSound.W.⊝-invol-norm
d_'8861''45'invol'45'norm_292 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_292 = erased
-- Once.Adequacy.LiftSound.∧-l
d_'8743''45'l_298 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'l_298 = erased
-- Once.Adequacy.LiftSound.∧-r
d_'8743''45'r_304 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'r_304 = erased
-- Once.Adequacy.LiftSound.Val
d_Val_312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Val_312 = erased
-- Once.Adequacy.LiftSound.plumbing-val
d_plumbing'45'val_330 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plumbing'45'val_330 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_plumbing'45'val_330 v3 v4 v6
du_plumbing'45'val_330 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_plumbing'45'val_330 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> let v8
                 = coe du_plumbing'45'val_330 (coe v4) (coe v7) (coe v2) in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> coe du_plumbing'45'val_330 (coe v0) (coe v6) (coe v9)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> let v10
                        = coe du_plumbing'45'val_330 (coe v8) (coe v6) (coe v2) in
                  coe
                    (let v11 = coe du_plumbing'45'val_330 (coe v9) (coe v7) (coe v2) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                           (coe v14))
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) erased
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) erased
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.rd
d_rd_426 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> Maybe Integer
d_rd_426 ~v0 ~v1 v2 v3 v4 = du_rd_426 v2 v3 v4
du_rd_426 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> Maybe Integer
du_rd_426 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         []
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_Int_30
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                MAlonzo.Code.Once.IRTy.C_Float_32
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                _ -> coe v3
         (:) v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
                  -> case coe v1 of
                       MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe du_rd_426 (coe v5) (coe v6) (coe v8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v3
                MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                  -> case coe v1 of
                       MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe du_rd_426 (coe v5) (coe v7) (coe v9)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.LiftSound.PathAt
d_PathAt_456 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> AgdaAny -> ()
d_PathAt_456 = erased
-- Once.Adequacy.LiftSound.PathOK
d_PathOK_476 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> ()
d_PathOK_476 = erased
-- Once.Adequacy.LiftSound.path-sound
d_path'45'sound_500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path'45'sound_500 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_path'45'sound_500 v0 v1 v2 v3 v4 v5 v6
du_path'45'sound_500 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path'45'sound_500 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_path'45'ok_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
         (coe v3) (coe v4))
      (coe v5) (coe v6)
-- Once.Adequacy.LiftSound.path-ok
d_path'45'ok_514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_PView_186 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path'45'ok_514 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_path'45'ok_514 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_path'45'ok_514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_PView_186 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path'45'ok_514 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_pv'45'id_190
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_pv'45'fst_196
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_pv'45'snd_202
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_pv'45'pair_214
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v4 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v19 v20
                      -> case coe v6 of
                           (:) v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
                                    -> coe
                                         du_pair'45'l_554 (coe v0) (coe v1) (coe v2) (coe v14)
                                         (coe v15) (coe v19) (coe v20) (coe v22) (coe v7) (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Arith.Machine.Recognise.d_plumbing'63'_114
                                            (coe v2) (coe v15) (coe v20))
                                  MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                                    -> coe
                                         du_pair'45'r_608 (coe v0) (coe v1) (coe v2) (coe v14)
                                         (coe v15) (coe v19) (coe v20) (coe v22) (coe v7) (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Arith.Machine.Recognise.d_plumbing'63'_114
                                            (coe v2) (coe v14) (coe v19))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_pv'45'comp_226
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v15 v17 v18
               -> coe
                    du_comp_670 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v17)
                    (coe v18) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'path'45'through_264
                       (coe v15) (coe v3) (coe v17) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair-l
d_pair'45'l_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'l_554 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_pair'45'l_554 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_pair'45'l_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'l_554 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
        -> let v11
                 = coe
                     du_path'45'ok_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
                        (coe v3) (coe v5))
                     (coe v7) (coe v8) (coe v9) in
           coe
             (let v12 = coe du_plumbing'45'val_330 (coe v4) (coe v6) (coe v9) in
              coe
                (case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                     -> case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                           (coe v17))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                           (coe v16))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair-r
d_pair'45'r_608 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'r_608 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_pair'45'r_608 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_pair'45'r_608 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'r_608 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
        -> let v11
                 = coe du_plumbing'45'val_330 (coe v3) (coe v5) (coe v9) in
           coe
             (let v12
                    = coe
                        du_path'45'ok_514 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                        (coe
                           MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
                           (coe v4) (coe v6))
                        (coe v7) (coe v8) (coe v9) in
              coe
                (case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                     -> case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                           (coe v18))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.comp
d_comp_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_comp_670 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_comp_670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_comp_670 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_comp_670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> let v12
                 = coe
                     du_path'45'ok_514 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
                        (coe v4) (coe v6))
                     (coe v11) (coe v8) (coe v9) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (let v15
                              = coe
                                  du_path'45'ok_514 (coe v0) (coe v1) (coe v4) (coe v3) (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242
                                     (coe v4) (coe v3) (coe v5))
                                  (coe v7) (coe v11) (coe v13) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                               -> coe
                                    seq (coe v17)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          erased))
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.toM
d_toM_730 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toM_730 ~v0 ~v1 v2 v3 = du_toM_730 v2 v3
du_toM_730 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
du_toM_730 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
      (coe
         MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_shape'45'as'45'type'45'base_540
         (coe v0))
      (coe v1)
-- Once.Adequacy.LiftSound.subst-×
d_subst'45''215'_760 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''215'_760 = erased
-- Once.Adequacy.LiftSound.toM-pair
d_toM'45'pair_774 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toM'45'pair_774 = erased
-- Once.Adequacy.LiftSound.leaf-sound
d_leaf'45'sound_794 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leaf'45'sound_794 = erased
-- Once.Adequacy.LiftSound._.go
d_go_822 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_822 = erased
-- Once.Adequacy.LiftSound._.go
d_go_854 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_854 = erased
-- Once.Adequacy.LiftSound.sz
d_sz_868 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_sz_868 ~v0 ~v1 ~v2 v3 v4 = du_sz_868 v3 v4
du_sz_868 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_sz_868 v0 v1
  = let v2 = 1 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
           -> coe
                addInt
                (coe
                   addInt
                   (coe addInt (coe (1 :: Integer)) (coe du_sz_868 (coe v0) (coe v6)))
                   (coe du_sz_868 (coe v0) (coe v6)))
                (coe du_sz_868 (coe v4) (coe v7))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       addInt
                       (coe addInt (coe (1 :: Integer)) (coe du_sz_868 (coe v8) (coe v6)))
                       (coe du_sz_868 (coe v9) (coe v7))
                _ -> coe v2
         _ -> coe v2)
-- Once.Adequacy.LiftSound.reassoc-<
d_reassoc'45''60'_902 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reassoc'45''60'_902 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_reassoc'45''60'_902 v3 v4 v5 v6 v7 v8
du_reassoc'45''60'_902 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_reassoc'45''60'_902 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_bound_920 (coe du_sz_868 (coe v2) (coe v3))
            (coe du_sz_868 (coe v1) (coe v4))
            (coe du_sz_868 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.bound
d_bound_920 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound_920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_bound_920 v9 v10 v11
du_bound_920 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound_920 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe du_step_954 (coe v0) (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        addInt
                        (coe
                           addInt
                           (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                           (coe v0))
                        (coe v0))
                     (coe v1))
                  (coe v1))
               (coe v2))))
-- Once.Adequacy.LiftSound._._.lhs≡
d_lhs'8801'_938 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lhs'8801'_938 = erased
-- Once.Adequacy.LiftSound._._.rhs≡
d_rhs'8801'_946 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rhs'8801'_946 = erased
-- Once.Adequacy.LiftSound._._.step
d_step_954 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_step_954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           v13 v14
  = du_step_954 v12 v13 v14
du_step_954 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step_954 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               addInt
               (coe
                  addInt (coe addInt (coe addInt (coe v0) (coe v0)) (coe v1))
                  (coe v1))
               (coe v2)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               addInt
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        addInt (coe addInt (coe addInt (coe v0) (coe v0)) (coe v0))
                        (coe v0))
                     (coe v1))
                  (coe v1))
               (coe v2))))
-- Once.Adequacy.LiftSound.assoc
d_assoc_976 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_976 = erased
-- Once.Adequacy.LiftSound.<-≤
d_'60''45''8804'_990 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804'_990 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'60''45''8804'_990 v5 v6
du_'60''45''8804'_990 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804'_990 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.Adequacy.LiftSound.sz-sigop
d_sz'45'sigop_1006 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'sigop_1006 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_sz'45'sigop_1006 v2 v6
du_sz'45'sigop_1006 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'sigop_1006 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               du_sz_868 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  du_sz_868 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe v1)))))
-- Once.Adequacy.LiftSound.sz-pairˡ
d_sz'45'pair'737'_1022 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'737'_1022 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6
  = du_sz'45'pair'737'_1022 v3 v5
du_sz'45'pair'737'_1022 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'737'_1022 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe du_sz_868 (coe v0) (coe v1)))
-- Once.Adequacy.LiftSound.sz-pairʳ
d_sz'45'pair'691'_1038 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'691'_1038 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_sz'45'pair'691'_1038 v4 v6
du_sz'45'pair'691'_1038 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'691'_1038 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe du_sz_868 (coe v0) (coe v1)))
-- Once.Adequacy.LiftSound.sz-distˡ
d_sz'45'dist'737'_1058 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'737'_1058 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_sz'45'dist'737'_1058 v2 v3 v4 v6 v7 v8
du_sz'45'dist'737'_1058 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'737'_1058 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_1084 (coe du_sz_868 (coe v1) (coe v3))
            (coe du_sz_868 (coe v2) (coe v4))
            (coe du_sz_868 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.e
d_e_1076 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e_1076 = erased
-- Once.Adequacy.LiftSound._.go
d_go_1084 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_go_1084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_go_1084 v9 v10 v11
du_go_1084 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_1084 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe addInt (coe addInt (coe v0) (coe v0)) (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
-- Once.Adequacy.LiftSound.sz-distʳ
d_sz'45'dist'691'_1106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'691'_1106 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_sz'45'dist'691'_1106 v2 v3 v4 v6 v7 v8
du_sz'45'dist'691'_1106 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'691'_1106 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_1132 (coe du_sz_868 (coe v1) (coe v3))
            (coe du_sz_868 (coe v2) (coe v4))
            (coe du_sz_868 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.e
d_e_1124 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e_1124 = erased
-- Once.Adequacy.LiftSound._.go
d_go_1132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_go_1132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_go_1132 v9 v10 v11
du_go_1132 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_1132 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe addInt (coe addInt (coe v1) (coe v1)) (coe v2)))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0))
                  (coe v1))
               (coe v1))
            (coe v2)))
-- Once.Adequacy.LiftSound.term-at
d_term'45'at_1148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_TView_128 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_term'45'at_1148 = erased
-- Once.Adequacy.LiftSound.term-val
d_term'45'val_1188 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_term'45'val_1188 = erased
-- Once.Adequacy.LiftSound.through
d_through_1208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_through_1208 = erased
-- Once.Adequacy.LiftSound.pair-val
d_pair'45'val_1240 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'val_1240 = erased
-- Once.Adequacy.LiftSound.BodyAt
d_BodyAt_1270 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny -> ()
d_BodyAt_1270 = erased
-- Once.Adequacy.LiftSound.BinAt
d_BinAt_1290 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny -> ()
d_BinAt_1290 = erased
-- Once.Adequacy.LiftSound.body-sound
d_body'45'sound_1318 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_body'45'sound_1318 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = subInt (coe v2) (coe (1 :: Integer)) in
    coe
      (coe
         (\ v9 v10 ->
            coe
              du_body'45'at_1334 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
              (coe v5)
              (coe
                 MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                 (coe v5))
              (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.LiftSound.body-at
d_body'45'at_1334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_body'45'at_1334 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_body'45'at_1334 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_body'45'at_1334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_body'45'at_1334 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'reassoc_358
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25 v26
                      -> let v27
                               = coe
                                   d_body'45'sound_1318 v0 v1 v2 v3 v4
                                   (coe
                                      MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25
                                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v18 v26 v21))
                                   (coe
                                      du_'60''45''8804'_990
                                      (coe
                                         du_reassoc'45''60'_902 (coe v18) (coe v23) (coe v4)
                                         (coe v25) (coe v26) (coe v21))
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'pred_2980 v2
                                         v7))
                                   v8 erased v9 in
                         coe
                           (case coe v27 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                -> case coe v29 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v28)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe v31))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'sigop_370
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v16 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.IR.C_SigOp_130 v20 v21 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186 v23 v24 v25 v26
                             -> coe
                                  du_sig'45'at_1358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                                  (coe v25) (coe v26) (coe v19)
                                  (coe
                                     du_'60''45''8804'_990
                                     (coe du_sz'45'sigop_1006 (coe v20) (coe v19))
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45'pred_2980 v2
                                        v7))
                                  (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'cint_378
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v14 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.IR.C_const_124 v19 v20
                      -> coe
                           du_lit_1520 (coe v0) (coe v20)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.du_is'45'terminal'63'_178
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'other_394
        -> coe
             du_path_1546 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v9)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'path_258
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                      (coe v3)))
                (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.sig-at
d_sig'45'at_1358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sig'45'at_1358 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14
  = du_sig'45'at_1358 v0 v1 v2 v3 v7 v8 v9 v10 v11 v14
du_sig'45'at_1358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sig'45'at_1358 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.SigOp.Info.C_primV_158 v10
        -> case coe v10 of
             MAlonzo.Code.Once.Arith.Prim.C_p'45'add_388
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1384 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop_470
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_390
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1384 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop_470
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_392
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1384 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop_470
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'div_394
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1384 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop_470
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_396
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1384 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop_470
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                                          (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_398
               -> coe
                    seq (coe v5)
                    (coe
                       seq (coe v6)
                       (coe
                          du_neg_1708 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                   (coe v3)))
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.bin-case
d_bin'45'case_1384 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_386 ->
  (MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10) ->
  (MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin'45'case_1384 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12
                   ~v13 v14
  = du_bin'45'case_1384 v0 v1 v2 v3 v5 v8 v9 v11 v14
du_bin'45'case_1384 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_386 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'case_1384 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             seq (coe v9)
             (let v10
                    = coe
                        du_bin'45'sound_1400 (coe v0) (coe v1) (coe v2) (coe v3)
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'42'__20
                           (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                           (coe MAlonzo.Code.Once.IRTy.C_Int_30))
                        (coe v5) (coe v6) (coe v8) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                     -> coe
                          seq (coe v11)
                          (case coe v12 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                               -> coe
                                    seq (coe v14)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
                                          (coe MAlonzo.Code.Once.Type.C_Int_134)
                                          (coe
                                             MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
                                          (coe
                                             MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
                                             (coe MAlonzo.Code.Once.Type.C_Int_134)
                                             (coe
                                                MAlonzo.Code.Once.Arith.Prim.du_primSem_416 v4 v0
                                                (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'42'__124
                                                      (coe MAlonzo.Code.Once.Type.C_Int_134)
                                                      (coe MAlonzo.Code.Once.Type.C_Int_134))
                                                   (coe
                                                      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202))
                                                   (coe v11)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          erased))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.bin-sound
d_bin'45'sound_1400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin'45'sound_1400 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_bin'45'sound_1400 v0 v1 v2 v3 v4 v5 v6 v10
du_bin'45'sound_1400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'sound_1400 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_bin'45'at_1418 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.du_b'45'view_84 (coe v4)
         (coe v5))
      (coe v6) (coe v7)
-- Once.Adequacy.LiftSound.bin-at
d_bin'45'at_1418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin'45'at_1418 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_bin'45'at_1418 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_bin'45'at_1418 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'at_1418 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'pair_48
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v19 v20
                      -> coe
                           du_pair_1838 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                           (coe v15) (coe v19) (coe v20) (coe v7) (coe v8)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v14) (coe v19))
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v15) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'dist_64
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v19 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v26 v27
                             -> coe
                                  du_dist_1898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                  (coe v16) (coe v17) (coe v26) (coe v27) (coe v22) (coe v7)
                                  (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Recognise.d_plumbing'63'_114
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                           (coe v3)))
                                     (coe v19) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'id_68
        -> coe
             du_ids_1978 (coe v8)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.lit
d_lit_1520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lit_1520 v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_lit_1520 v0 v4 v10
du_lit_1520 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lit_1520 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Word.d_fromℤ_20
            (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v0))
            (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Adequacy.LiftSound._.path
d_path_1546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path_1546 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_path_1546 v0 v1 v3 v4 v5 v9 v10
du_path_1546 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path_1546 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_typed_1562 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v7)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._._.typed
d_typed_1562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typed_1562 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
             v14 ~v15 ~v16
  = du_typed_1562 v0 v1 v3 v4 v5 v9 v10 v14
du_typed_1562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typed_1562 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (let v8
             = coe
                 du_path'45'ok_514 (coe v0) (coe v1)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                       (coe v2)))
                 (coe v3) (coe v4)
                 (coe
                    MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                          (coe v2)))
                    (coe v3) (coe v4))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
                 (coe v5) in
       coe
         (case coe v8 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
              -> case coe v10 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) erased)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.LiftSound._.neg
d_neg_1708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_neg_1708 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_neg_1708 v0 v1 v2 v3 v5 v6 v9 v10
du_neg_1708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_neg_1708 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = coe
                     d_body'45'sound_1318 v0 v1 v2 v3
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                        (coe MAlonzo.Code.Once.Type.C_Int_134))
                     v4 v5 v8 erased v6 in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> coe
                       seq (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
                             (coe MAlonzo.Code.Once.Type.C_Int_134)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe
                                   MAlonzo.Code.Once.Arith.Prim.du_primSem_416
                                   (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_398) v0
                                   (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
                                      (coe MAlonzo.Code.Once.Type.C_Int_134)
                                      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
                                      (coe v10)))))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair
d_pair_1838 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_pair_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 v15
du_pair_1838 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair_1838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
               -> let v14
                        = coe
                            d_body'45'sound_1318 v0 v1 v2 v3 v4 v6
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                               (coe
                                  du_sz_868
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                  (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                               (coe du_sz'45'pair'737'_1022 (coe v4) (coe v6)) (coe v8))
                            v12 erased v9 in
                  coe
                    (let v15
                           = coe
                               d_body'45'sound_1318 v0 v1 v2 v3 v5 v7
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_868
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                     (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                                  (coe du_sz'45'pair'691'_1038 (coe v5) (coe v7)) (coe v8))
                               v13 erased v9 in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                            -> case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                          -> case coe v21 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v16) (coe v20))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v19) (coe v23)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.dist
d_dist_1898 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dist_1898 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_dist_1898 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v15
du_dist_1898 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dist_1898 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         du_pair_1916 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe
            MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
            (coe v3)
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                  (coe v3)))
            (coe v5) (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9))
         (coe
            MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
            (coe v3)
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                  (coe v3)))
            (coe v6) (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)))
-- Once.Adequacy.LiftSound._._.pair
d_pair_1916 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_1916 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_pair_1916 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v19 v21
du_pair_1916 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair_1916 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> let v16
                        = coe du_plumbing'45'val_330 (coe v4) (coe v9) (coe v11) in
                  coe
                    (let v17
                           = coe
                               d_body'45'sound_1318 v0 v1 v2 v3 v5
                               (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9)
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_868
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                        (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                        v9))
                                  (coe
                                     du_sz'45'dist'737'_1058 (coe v4) (coe v5) (coe v6) (coe v7)
                                     (coe v8) (coe v9))
                                  (coe v10))
                               v14 erased v11 in
                     coe
                       (let v18
                              = coe
                                  d_body'45'sound_1318 v0 v1 v2 v3 v6
                                  (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                     (coe
                                        du_sz_868
                                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                           v9))
                                     (coe
                                        du_sz'45'dist'691'_1106 (coe v4) (coe v5) (coe v6) (coe v7)
                                        (coe v8) (coe v9))
                                     (coe v10))
                                  v15 erased v11 in
                        coe
                          (coe
                             seq (coe v16)
                             (case coe v17 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                  -> case coe v20 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                         -> case coe v18 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                -> case coe v24 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v19) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               erased
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v22) (coe v26)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.ids
d_ids_1978 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ids_1978 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15
  = du_ids_1978 v8 v9 v11
du_ids_1978 ::
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ids_1978 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         seq (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
-- Once.Adequacy.LiftSound.fbody-sound
d_fbody'45'sound_2010 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbody'45'sound_2010 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = subInt (coe v2) (coe (1 :: Integer)) in
    coe
      (coe
         (\ v9 v10 ->
            coe
              du_fbody'45'at_2026 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
              (coe v5)
              (coe
                 MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                 (coe v5))
              (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.LiftSound.fbody-at
d_fbody'45'at_2026 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbody'45'at_2026 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_fbody'45'at_2026 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_fbody'45'at_2026 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbody'45'at_2026 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'reassoc_358
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25 v26
                      -> let v27
                               = coe
                                   d_fbody'45'sound_2010 v0 v1 v2 v3 v4
                                   (coe
                                      MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25
                                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v18 v26 v21))
                                   (coe
                                      du_'60''45''8804'_990
                                      (coe
                                         du_reassoc'45''60'_902 (coe v18) (coe v23) (coe v4)
                                         (coe v25) (coe v26) (coe v21))
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'pred_2980 v2
                                         v7))
                                   v8 erased v9 in
                         coe
                           (case coe v27 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                -> case coe v29 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v28)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe v31))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'sigop_370
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v16 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.IR.C_SigOp_130 v20 v21 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186 v23 v24 v25 v26
                             -> coe
                                  du_fsig'45'at_2050 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                                  (coe v25) (coe v26) (coe v19)
                                  (coe
                                     du_'60''45''8804'_990
                                     (coe du_sz'45'sigop_1006 (coe v20) (coe v19))
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45'pred_2980 v2
                                        v7))
                                  (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'cflt_386
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v14 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.IR.C_const_124 v19 v20
                      -> coe
                           du_lit_2212 (coe v0) (coe v20)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.du_is'45'terminal'63'_178
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'other_394
        -> coe
             du_path_2238 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v9)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'path_258
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                      (coe v3)))
                (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.fsig-at
d_fsig'45'at_2050 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fsig'45'at_2050 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 ~v12
                  ~v13 v14
  = du_fsig'45'at_2050 v0 v1 v2 v3 v7 v8 v9 v10 v11 v14
du_fsig'45'at_2050 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fsig'45'at_2050 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.SigOp.Info.C_primV_158 v10
        -> case coe v10 of
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_400
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_2076 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop'45'float_630
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_402
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_2076 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop'45'float_630
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_404
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_2076 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop'45'float_630
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_406
               -> case coe v5 of
                    MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_2076 (coe v0) (coe v1) (coe v2) (coe v3)
                                    (coe v10) (coe v7) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'binop'45'float_630
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                                          (coe MAlonzo.Code.Once.IRTy.C_Float_32))
                                       (coe v7))
                                    (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_408
               -> coe
                    seq (coe v5)
                    (coe
                       seq (coe v6)
                       (coe
                          du_conv_2380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body_462
                             (coe v3)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe
                                   MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                   (coe v3)))
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.fbin-case
d_fbin'45'case_2076 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_386 ->
  (MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10) ->
  (MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbin'45'case_2076 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12
                    ~v13 v14
  = du_fbin'45'case_2076 v0 v1 v2 v3 v5 v8 v9 v11 v14
du_fbin'45'case_2076 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_386 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'case_2076 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             seq (coe v9)
             (let v10
                    = coe
                        du_fbin'45'sound_2092 (coe v0) (coe v1) (coe v2) (coe v3)
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'42'__20
                           (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                           (coe MAlonzo.Code.Once.IRTy.C_Float_32))
                        (coe v5) (coe v6) (coe v8) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                     -> coe
                          seq (coe v11)
                          (case coe v12 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                               -> coe
                                    seq (coe v14)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
                                          (coe MAlonzo.Code.Once.Type.C_Float_136)
                                          (coe
                                             MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
                                          (coe
                                             MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
                                             (coe MAlonzo.Code.Once.Type.C_Float_136)
                                             (coe
                                                MAlonzo.Code.Once.Arith.Prim.du_primSem_416 v4 v0
                                                (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'42'__124
                                                      (coe MAlonzo.Code.Once.Type.C_Float_136)
                                                      (coe MAlonzo.Code.Once.Type.C_Float_136))
                                                   (coe
                                                      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204))
                                                   (coe v11)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          erased))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.fbin-sound
d_fbin'45'sound_2092 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbin'45'sound_2092 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_fbin'45'sound_2092 v0 v1 v2 v3 v4 v5 v6 v10
du_fbin'45'sound_2092 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'sound_2092 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_fbin'45'at_2110 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.du_b'45'view_84 (coe v4)
         (coe v5))
      (coe v6) (coe v7)
-- Once.Adequacy.LiftSound.fbin-at
d_fbin'45'at_2110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbin'45'at_2110 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_fbin'45'at_2110 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_fbin'45'at_2110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'at_2110 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'pair_48
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v19 v20
                      -> coe
                           du_pair_2510 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                           (coe v15) (coe v19) (coe v20) (coe v7) (coe v8)
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body'45'float_622
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v14) (coe v19))
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body'45'float_622
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                    (coe v3)))
                              (coe v15) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'dist_64
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v19 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v26 v27
                             -> coe
                                  du_dist_2570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                  (coe v16) (coe v17) (coe v26) (coe v27) (coe v22) (coe v7)
                                  (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Recognise.d_plumbing'63'_114
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                                           (coe v3)))
                                     (coe v19) (coe v22))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'id_68
        -> coe
             du_ids_2650 (coe v8)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v3)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.lit
d_lit_2212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lit_2212 v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_lit_2212 v0 v4 v10
du_lit_2212 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lit_2212 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Float.Decimal.d_round_174
            (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v0))
            (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Adequacy.LiftSound._.path
d_path_2238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path_2238 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_path_2238 v0 v1 v3 v4 v5 v9 v10
du_path_2238 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path_2238 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_typed_2254 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v7)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._._.typed
d_typed_2254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typed_2254 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
             v14 ~v15 ~v16
  = du_typed_2254 v0 v1 v3 v4 v5 v9 v10 v14
du_typed_2254 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typed_2254 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (let v8
             = coe
                 du_path'45'ok_514 (coe v0) (coe v1)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                       (coe v2)))
                 (coe v3) (coe v4)
                 (coe
                    MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                       (coe
                          MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                          (coe v2)))
                    (coe v3) (coe v4))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6)
                 (coe v5) in
       coe
         (case coe v8 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
              -> case coe v10 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) erased)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.LiftSound._.conv
d_conv_2380 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_conv_2380 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_conv_2380 v0 v1 v2 v3 v5 v6 v9 v10
du_conv_2380 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conv_2380 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = coe
                     d_body'45'sound_1318 v0 v1 v2 v3
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                        (coe MAlonzo.Code.Once.Type.C_Int_134))
                     v4 v5 v8 erased v6 in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> coe
                       seq (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
                             (coe MAlonzo.Code.Once.Type.C_Float_136)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204)
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_erase'7501'_92
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe
                                   MAlonzo.Code.Once.Arith.Prim.du_primSem_416
                                   (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_408) v0
                                   (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
                                      (coe MAlonzo.Code.Once.Type.C_Int_134)
                                      (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202)
                                      (coe v10)))))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair
d_pair_2510 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_2510 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_pair_2510 v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 v15
du_pair_2510 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair_2510 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
               -> let v14
                        = coe
                            d_fbody'45'sound_2010 v0 v1 v2 v3 v4 v6
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                               (coe
                                  du_sz_868
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                  (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                               (coe du_sz'45'pair'737'_1022 (coe v4) (coe v6)) (coe v8))
                            v12 erased v9 in
                  coe
                    (let v15
                           = coe
                               d_fbody'45'sound_2010 v0 v1 v2 v3 v5 v7
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_868
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                     (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                                  (coe du_sz'45'pair'691'_1038 (coe v5) (coe v7)) (coe v8))
                               v13 erased v9 in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                            -> case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                          -> case coe v21 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v16) (coe v20))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v19) (coe v23)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.dist
d_dist_2570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dist_2570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_dist_2570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v15
du_dist_2570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dist_2570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         du_pair_2588 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe
            MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body'45'float_622
            (coe v3)
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                  (coe v3)))
            (coe v5) (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9))
         (coe
            MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'body'45'float_622
            (coe v3)
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
               (coe
                  MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
                  (coe v3)))
            (coe v6) (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)))
-- Once.Adequacy.LiftSound._._.pair
d_pair_2588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair_2588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_pair_2588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v19 v21
du_pair_2588 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair_2588 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> let v16
                        = coe du_plumbing'45'val_330 (coe v4) (coe v9) (coe v11) in
                  coe
                    (let v17
                           = coe
                               d_fbody'45'sound_2010 v0 v1 v2 v3 v5
                               (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9)
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_868
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                        (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                        v9))
                                  (coe
                                     du_sz'45'dist'737'_1058 (coe v4) (coe v5) (coe v6) (coe v7)
                                     (coe v8) (coe v9))
                                  (coe v10))
                               v14 erased v11 in
                     coe
                       (let v18
                              = coe
                                  d_fbody'45'sound_2010 v0 v1 v2 v3 v6
                                  (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                     (coe
                                        du_sz_868
                                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                           v9))
                                     (coe
                                        du_sz'45'dist'691'_1106 (coe v4) (coe v5) (coe v6) (coe v7)
                                        (coe v8) (coe v9))
                                     (coe v10))
                                  v15 erased v11 in
                        coe
                          (coe
                             seq (coe v16)
                             (case coe v17 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                  -> case coe v20 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                         -> case coe v18 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                -> case coe v24 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v19) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               erased
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v22) (coe v26)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.ids
d_ids_2650 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ids_2650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15
  = du_ids_2650 v8 v9 v11
du_ids_2650 ::
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ids_2650 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         seq (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
-- Once.Adequacy.LiftSound.block-int
d_block'45'int_2676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'int_2676 = erased
-- Once.Adequacy.LiftSound.block-flt
d_block'45'flt_2690 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'flt_2690 = erased
-- Once.Adequacy.LiftSound.just-int
d_just'45'int_2702 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'int_2702 = erased
-- Once.Adequacy.LiftSound.just-flt
d_just'45'flt_2708 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'flt_2708 = erased
-- Once.Adequacy.LiftSound.lift-sound
d_lift'45'sound_2720 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'sound_2720 = erased
-- Once.Adequacy.LiftSound._.with-body
d_with'45'body_2810 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_with'45'body_2810 = erased
-- Once.Adequacy.LiftSound._.with-body
d_with'45'body_2910 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_with'45'body_2910 = erased
