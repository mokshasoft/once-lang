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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Recognise
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.LiftSound.M.⟦_⟧
d_'10214'_'10215'_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_50 = erased
-- Once.Adequacy.LiftSound.W._%ˢ_
d__'37''738'__64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__64 ~v0 ~v1 v2 = du__'37''738'__64 v2
du__'37''738'__64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
du__'37''738'__64 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W._/ˢ_
d__'47''738'__66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__66 ~v0 ~v1 v2 = du__'47''738'__66 v2
du__'47''738'__66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
du__'47''738'__66 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W._<ˢ_
d__'60''738'__68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__68 ~v0 ~v1 v2 = du__'60''738'__68 v2
du__'60''738'__68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
du__'60''738'__68 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W._divℕ_
d__divℕ__70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__70 ~v0 ~v1 ~v2 = du__divℕ__70
du__divℕ__70 :: Integer -> Integer -> Integer
du__divℕ__70 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Adequacy.LiftSound.W._modℕ_
d__modℕ__72 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__72 ~v0 ~v1 ~v2 = du__modℕ__72
du__modℕ__72 :: Integer -> Integer -> Integer
du__modℕ__72 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Adequacy.LiftSound.W._≡ʷ_
d__'8801''695'__74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__74 ~v0 ~v1 ~v2 = du__'8801''695'__74
du__'8801''695'__74 :: Integer -> Integer -> Bool
du__'8801''695'__74
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Adequacy.LiftSound.W._⊕_
d__'8853'__76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__76 ~v0 ~v1 v2 = du__'8853'__76 v2
du__'8853'__76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
du__'8853'__76 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W._⊖_
d__'8854'__78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__78 ~v0 ~v1 v2 = du__'8854'__78 v2
du__'8854'__78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
du__'8854'__78 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W._⊗_
d__'8855'__80 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__80 ~v0 ~v1 v2 = du__'8855'__80 v2
du__'8855'__80 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
du__'8855'__80 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.InRange
d_InRange_82 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_82 = erased
-- Once.Adequacy.LiftSound.W.Word
d_Word_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_84 = erased
-- Once.Adequacy.LiftSound.W.fromℤ
d_fromℤ_86 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_86 ~v0 ~v1 v2 = du_fromℤ_86 v2
du_fromℤ_86 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
du_fromℤ_86 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.half
d_half_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_88 ~v0 ~v1 v2 = du_half_88 v2
du_half_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
du_half_88 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.inRange?
d_inRange'63'_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_90 ~v0 ~v1 v2 = du_inRange'63'_90 v2
du_inRange'63'_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inRange'63'_90 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.intMin
d_intMin_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_92 ~v0 ~v1 v2 = du_intMin_92 v2
du_intMin_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
du_intMin_92 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.modulus
d_modulus_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_94 ~v0 ~v1 v2 = du_modulus_94 v2
du_modulus_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
du_modulus_94 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.modulus≢0
d_modulus'8802'0_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_96 ~v0 ~v1 v2 = du_modulus'8802'0_96 v2
du_modulus'8802'0_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_modulus'8802'0_96 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.negOne
d_negOne_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_98 ~v0 ~v1 v2 = du_negOne_98 v2
du_negOne_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
du_negOne_98 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.norm
d_norm_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_100 ~v0 ~v1 v2 = du_norm_100 v2
du_norm_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
du_norm_100 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.tdivℤ
d_tdivℤ_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_102 ~v0 ~v1 ~v2 = du_tdivℤ_102
du_tdivℤ_102 :: Integer -> Integer -> Integer
du_tdivℤ_102 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Adequacy.LiftSound.W.tmodℤ
d_tmodℤ_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_104 ~v0 ~v1 ~v2 = du_tmodℤ_104
du_tmodℤ_104 :: Integer -> Integer -> Integer
du_tmodℤ_104 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Adequacy.LiftSound.W.toWord
d_toWord_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_106 ~v0 ~v1 v2 = du_toWord_106 v2
du_toWord_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_toWord_106 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Adequacy.LiftSound.W.toℤ
d_toℤ_108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_108 ~v0 ~v1 v2 = du_toℤ_108 v2
du_toℤ_108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
du_toℤ_108 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.W.⊝_
d_'8861'__110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__110 ~v0 ~v1 v2 = du_'8861'__110 v2
du_'8861'__110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
du_'8861'__110 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Adequacy.LiftSound.∧-l
d_'8743''45'l_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'l_116 = erased
-- Once.Adequacy.LiftSound.∧-r
d_'8743''45'r_122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'r_122 = erased
-- Once.Adequacy.LiftSound.Val
d_Val_130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Val_130 = erased
-- Once.Adequacy.LiftSound.plumbing-val
d_plumbing'45'val_148 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_plumbing'45'val_148 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_plumbing'45'val_148 v3 v4 v6
du_plumbing'45'val_148 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_plumbing'45'val_148 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> let v8
                 = coe du_plumbing'45'val_148 (coe v4) (coe v7) (coe v2) in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> coe du_plumbing'45'val_148 (coe v0) (coe v6) (coe v9)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> let v10
                        = coe du_plumbing'45'val_148 (coe v8) (coe v6) (coe v2) in
                  coe
                    (let v11 = coe du_plumbing'45'val_148 (coe v9) (coe v7) (coe v2) in
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
d_rd_244 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> Maybe Integer
d_rd_244 ~v0 ~v1 v2 v3 v4 = du_rd_244 v2 v3 v4
du_rd_244 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> Maybe Integer
du_rd_244 v0 v1 v2
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
                                -> coe du_rd_244 (coe v5) (coe v6) (coe v8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v3
                MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                  -> case coe v1 of
                       MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe du_rd_244 (coe v5) (coe v7) (coe v9)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.LiftSound.PathAt
d_PathAt_274 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> AgdaAny -> ()
d_PathAt_274 = erased
-- Once.Adequacy.LiftSound.PathOK
d_PathOK_294 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> ()
d_PathOK_294 = erased
-- Once.Adequacy.LiftSound.path-sound
d_path'45'sound_318 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path'45'sound_318 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_path'45'sound_318 v0 v1 v2 v3 v4 v5 v6
du_path'45'sound_318 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path'45'sound_318 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_path'45'ok_332 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
         (coe v3) (coe v4))
      (coe v5) (coe v6)
-- Once.Adequacy.LiftSound.path-ok
d_path'45'ok_332 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_PView_186 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_path'45'ok_332 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_path'45'ok_332 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_path'45'ok_332 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_PView_186 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path'45'ok_332 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                         du_pair'45'l_372 (coe v0) (coe v1) (coe v2) (coe v14)
                                         (coe v15) (coe v19) (coe v20) (coe v22) (coe v7) (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Arith.Machine.Recognise.d_plumbing'63'_114
                                            (coe v2) (coe v15) (coe v20))
                                  MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
                                    -> coe
                                         du_pair'45'r_426 (coe v0) (coe v1) (coe v2) (coe v14)
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
                    du_comp_488 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v17)
                    (coe v18) (coe v6) (coe v7) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Arith.Machine.Recognise.d_recognise'45'path'45'through_264
                       (coe v15) (coe v3) (coe v17) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair-l
d_pair'45'l_372 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair'45'l_372 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_pair'45'l_372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_pair'45'l_372 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'l_372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
        -> let v11
                 = coe
                     du_path'45'ok_332 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.Recognise.d_p'45'view_242 (coe v2)
                        (coe v3) (coe v5))
                     (coe v7) (coe v8) (coe v9) in
           coe
             (let v12 = coe du_plumbing'45'val_148 (coe v4) (coe v6) (coe v9) in
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
d_pair'45'r_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair'45'r_426 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_pair'45'r_426 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_pair'45'r_426 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'r_426 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
        -> let v11
                 = coe du_plumbing'45'val_148 (coe v3) (coe v5) (coe v9) in
           coe
             (let v12
                    = coe
                        du_path'45'ok_332 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
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
d_comp_488 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_comp_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13
  = du_comp_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11
du_comp_488 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_comp_488 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> let v12
                 = coe
                     du_path'45'ok_332 (coe v0) (coe v1) (coe v2) (coe v4) (coe v6)
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
                                  du_path'45'ok_332 (coe v0) (coe v1) (coe v4) (coe v3) (coe v5)
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
d_toM_548 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toM_548 ~v0 ~v1 v2 v3 = du_toM_548 v2 v3
du_toM_548 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
du_toM_548 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
      (coe
         MAlonzo.Code.Once.Arith.Machine.IR.d_shape'45'as'45'type_158
         (coe v0))
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_shape'45'as'45'type'45'base_362
         (coe v0))
      (coe v1)
-- Once.Adequacy.LiftSound.subst-×
d_subst'45''215'_578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''215'_578 = erased
-- Once.Adequacy.LiftSound.toM-pair
d_toM'45'pair_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toM'45'pair_592 = erased
-- Once.Adequacy.LiftSound.leaf-sound
d_leaf'45'sound_612 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leaf'45'sound_612 = erased
-- Once.Adequacy.LiftSound._.go
d_go_640 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_go_640 = erased
-- Once.Adequacy.LiftSound._.go
d_go_672 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_go_672 = erased
-- Once.Adequacy.LiftSound.sz
d_sz_686 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_sz_686 ~v0 ~v1 ~v2 v3 v4 = du_sz_686 v3 v4
du_sz_686 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_sz_686 v0 v1
  = let v2 = 1 :: Integer in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
           -> coe
                addInt
                (coe
                   addInt
                   (coe addInt (coe (1 :: Integer)) (coe du_sz_686 (coe v0) (coe v6)))
                   (coe du_sz_686 (coe v0) (coe v6)))
                (coe du_sz_686 (coe v4) (coe v7))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
           -> case coe v0 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       addInt
                       (coe addInt (coe (1 :: Integer)) (coe du_sz_686 (coe v8) (coe v6)))
                       (coe du_sz_686 (coe v9) (coe v7))
                _ -> coe v2
         _ -> coe v2)
-- Once.Adequacy.LiftSound.reassoc-<
d_reassoc'45''60'_720 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reassoc'45''60'_720 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_reassoc'45''60'_720 v3 v4 v5 v6 v7 v8
du_reassoc'45''60'_720 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_reassoc'45''60'_720 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_bound_738 (coe du_sz_686 (coe v2) (coe v3))
            (coe du_sz_686 (coe v1) (coe v4))
            (coe du_sz_686 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.bound
d_bound_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_bound_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_bound_738 v9 v10 v11
du_bound_738 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound_738 v0 v1 v2
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
         (coe du_step_772 (coe v0) (coe v1) (coe v2))
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
d_lhs'8801'_756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_lhs'8801'_756 = erased
-- Once.Adequacy.LiftSound._._.rhs≡
d_rhs'8801'_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_rhs'8801'_764 = erased
-- Once.Adequacy.LiftSound._._.step
d_step_772 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_step_772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           v13 v14
  = du_step_772 v12 v13 v14
du_step_772 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_step_772 v0 v1 v2
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
d_assoc_794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_794 = erased
-- Once.Adequacy.LiftSound.<-≤
d_'60''45''8804'_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804'_808 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'60''45''8804'_808 v5 v6
du_'60''45''8804'_808 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804'_808 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.Adequacy.LiftSound.sz-sigop
d_sz'45'sigop_824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'sigop_824 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_sz'45'sigop_824 v2 v6
du_sz'45'sigop_824 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'sigop_824 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               du_sz_686 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  du_sz_686 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                  (coe v1)))))
-- Once.Adequacy.LiftSound.sz-pairˡ
d_sz'45'pair'737'_840 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'737'_840 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6
  = du_sz'45'pair'737'_840 v3 v5
du_sz'45'pair'737'_840 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'737'_840 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe du_sz_686 (coe v0) (coe v1)))
-- Once.Adequacy.LiftSound.sz-pairʳ
d_sz'45'pair'691'_856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'pair'691'_856 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_sz'45'pair'691'_856 v4 v6
du_sz'45'pair'691'_856 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'pair'691'_856 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe du_sz_686 (coe v0) (coe v1)))
-- Once.Adequacy.LiftSound.sz-distˡ
d_sz'45'dist'737'_876 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'737'_876 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_sz'45'dist'737'_876 v2 v3 v4 v6 v7 v8
du_sz'45'dist'737'_876 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'737'_876 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_902 (coe du_sz_686 (coe v1) (coe v3))
            (coe du_sz_686 (coe v2) (coe v4))
            (coe du_sz_686 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.e
d_e_894 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_e_894 = erased
-- Once.Adequacy.LiftSound._.go
d_go_902 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_go_902 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_go_902 v9 v10 v11
du_go_902 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_902 v0 v1 v2
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
d_sz'45'dist'691'_924 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sz'45'dist'691'_924 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_sz'45'dist'691'_924 v2 v3 v4 v6 v7 v8
du_sz'45'dist'691'_924 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sz'45'dist'691'_924 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            du_go_950 (coe du_sz_686 (coe v1) (coe v3))
            (coe du_sz_686 (coe v2) (coe v4))
            (coe du_sz_686 (coe v0) (coe v5))))
-- Once.Adequacy.LiftSound._.e
d_e_942 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_e_942 = erased
-- Once.Adequacy.LiftSound._.go
d_go_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_go_950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_go_950 v9 v10 v11
du_go_950 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_950 v0 v1 v2
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
d_term'45'at_966 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_TView_128 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_term'45'at_966 = erased
-- Once.Adequacy.LiftSound.term-val
d_term'45'val_1006 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_term'45'val_1006 = erased
-- Once.Adequacy.LiftSound.through
d_through_1026 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_through_1026 = erased
-- Once.Adequacy.LiftSound.pair-val
d_pair'45'val_1058 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair'45'val_1058 = erased
-- Once.Adequacy.LiftSound.BodyAt
d_BodyAt_1088 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny -> ()
d_BodyAt_1088 = erased
-- Once.Adequacy.LiftSound.BinAt
d_BinAt_1108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> AgdaAny -> ()
d_BinAt_1108 = erased
-- Once.Adequacy.LiftSound.body-sound
d_body'45'sound_1136 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_body'45'sound_1136 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = subInt (coe v2) (coe (1 :: Integer)) in
    coe
      (coe
         (\ v9 v10 ->
            coe
              du_body'45'at_1152 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
              (coe v5)
              (coe
                 MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                 (coe v5))
              (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.LiftSound.body-at
d_body'45'at_1152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_body'45'at_1152 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_body'45'at_1152 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_body'45'at_1152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_body'45'at_1152 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'reassoc_358
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25 v26
                      -> let v27
                               = coe
                                   d_body'45'sound_1136 v0 v1 v2 v3 v4
                                   (coe
                                      MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25
                                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v18 v26 v21))
                                   (coe
                                      du_'60''45''8804'_808
                                      (coe
                                         du_reassoc'45''60'_720 (coe v18) (coe v23) (coe v4)
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
                    MAlonzo.Code.Once.IR.C_SigOp_132 v20 v21 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 v23 v24 v25 v26
                             -> coe
                                  du_sig'45'at_1176 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                                  (coe v25) (coe v26) (coe v19)
                                  (coe
                                     du_'60''45''8804'_808
                                     (coe du_sz'45'sigop_824 (coe v20) (coe v19))
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
                    MAlonzo.Code.Once.IR.C_const_126 v19 v20
                      -> coe
                           du_lit_1338 (coe v0) (coe v20)
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
             du_path_1364 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v9)
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
d_sig'45'at_1176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sig'45'at_1176 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 ~v12 ~v13
                 v14
  = du_sig'45'at_1176 v0 v1 v2 v3 v7 v8 v9 v10 v11 v14
du_sig'45'at_1176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sig'45'at_1176 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.SigOp.Info.C_primV_90 v10
        -> case coe v10 of
             MAlonzo.Code.Once.Arith.Prim.C_p'45'add_210
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1202 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_212
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1202 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_214
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1202 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'div_216
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1202 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_218
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_bin'45'case_1202 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_220
               -> coe
                    seq (coe v5)
                    (coe
                       seq (coe v6)
                       (coe
                          du_neg_1526 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
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
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.bin-case
d_bin'45'case_1202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208 ->
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
d_bin'45'case_1202 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12
                   ~v13 v14
  = du_bin'45'case_1202 v0 v1 v2 v3 v5 v8 v9 v11 v14
du_bin'45'case_1202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'case_1202 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             seq (coe v9)
             (let v10
                    = coe
                        du_bin'45'sound_1218 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
                                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                             (coe
                                                MAlonzo.Code.Once.Arith.Prim.du_primSem_238 v4 v0
                                                (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14))
                                                   (coe v11)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          erased))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.bin-sound
d_bin'45'sound_1218 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_bin'45'sound_1218 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_bin'45'sound_1218 v0 v1 v2 v3 v4 v5 v6 v10
du_bin'45'sound_1218 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'sound_1218 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_bin'45'at_1236 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.du_b'45'view_84 (coe v4)
         (coe v5))
      (coe v6) (coe v7)
-- Once.Adequacy.LiftSound.bin-at
d_bin'45'at_1236 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_bin'45'at_1236 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_bin'45'at_1236 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_bin'45'at_1236 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'at_1236 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'pair_48
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v19 v20
                      -> coe
                           du_pair_1656 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
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
                                  du_dist_1716 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
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
             du_ids_1796 (coe v8)
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
d_lit_1338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_lit_1338 v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_lit_1338 v0 v4 v10
du_lit_1338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lit_1338 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
            (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
            (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Adequacy.LiftSound._.path
d_path_1364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_path_1364 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_path_1364 v0 v1 v3 v4 v5 v9 v10
du_path_1364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path_1364 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_typed_1380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v7)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._._.typed
d_typed_1380 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_typed_1380 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
             v14 ~v15 ~v16
  = du_typed_1380 v0 v1 v3 v4 v5 v9 v10 v14
du_typed_1380 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typed_1380 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (let v8
             = coe
                 du_path'45'ok_332 (coe v0) (coe v1)
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
d_neg_1526 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_neg_1526 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_neg_1526 v0 v1 v2 v3 v5 v6 v9 v10
du_neg_1526 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_neg_1526 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = coe
                     d_body'45'sound_1136 v0 v1 v2 v3
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                     v4 v5 v8 erased v6 in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> coe
                       seq (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
                             (coe
                                MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe
                                   MAlonzo.Code.Once.Arith.Prim.du_primSem_238
                                   (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_220) v0
                                   (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
                                      (coe v10)))))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair
d_pair_1656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair_1656 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_pair_1656 v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 v15
du_pair_1656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_pair_1656 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
               -> let v14
                        = coe
                            d_body'45'sound_1136 v0 v1 v2 v3 v4 v6
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                               (coe
                                  du_sz_686
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                  (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                               (coe du_sz'45'pair'737'_840 (coe v4) (coe v6)) (coe v8))
                            v12 erased v9 in
                  coe
                    (let v15
                           = coe
                               d_body'45'sound_1136 v0 v1 v2 v3 v5 v7
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_686
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                     (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                                  (coe du_sz'45'pair'691'_856 (coe v5) (coe v7)) (coe v8))
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
d_dist_1716 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_dist_1716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_dist_1716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v15
du_dist_1716 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_dist_1716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         du_pair_1734 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
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
d_pair_1734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair_1734 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_pair_1734 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v19 v21
du_pair_1734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_pair_1734 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> let v16
                        = coe du_plumbing'45'val_148 (coe v4) (coe v9) (coe v11) in
                  coe
                    (let v17
                           = coe
                               d_body'45'sound_1136 v0 v1 v2 v3 v5
                               (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9)
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_686
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                        (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                        v9))
                                  (coe
                                     du_sz'45'dist'737'_876 (coe v4) (coe v5) (coe v6) (coe v7)
                                     (coe v8) (coe v9))
                                  (coe v10))
                               v14 erased v11 in
                     coe
                       (let v18
                              = coe
                                  d_body'45'sound_1136 v0 v1 v2 v3 v6
                                  (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                     (coe
                                        du_sz_686
                                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                           v9))
                                     (coe
                                        du_sz'45'dist'691'_924 (coe v4) (coe v5) (coe v6) (coe v7)
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
d_ids_1796 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_ids_1796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15
  = du_ids_1796 v8 v9 v11
du_ids_1796 ::
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ids_1796 v0 v1 v2
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
d_fbody'45'sound_1828 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fbody'45'sound_1828 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = subInt (coe v2) (coe (1 :: Integer)) in
    coe
      (coe
         (\ v9 v10 ->
            coe
              du_fbody'45'at_1844 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
              (coe v5)
              (coe
                 MAlonzo.Code.Once.Arith.Machine.Recognise.du_rb'45'view_402
                 (coe v5))
              (coe v6) (coe v7) (coe v10)))
-- Once.Adequacy.LiftSound.fbody-at
d_fbody'45'at_1844 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_fbody'45'at_1844 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_fbody'45'at_1844 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_fbody'45'at_1844 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_RBView_342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbody'45'at_1844 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_v'45'reassoc_358
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v18 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25 v26
                      -> let v27
                               = coe
                                   d_fbody'45'sound_1828 v0 v1 v2 v3 v4
                                   (coe
                                      MAlonzo.Code.Once.IR.C__'8728'__28 v23 v25
                                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v18 v26 v21))
                                   (coe
                                      du_'60''45''8804'_808
                                      (coe
                                         du_reassoc'45''60'_720 (coe v18) (coe v23) (coe v4)
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
                    MAlonzo.Code.Once.IR.C_SigOp_132 v20 v21 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 v23 v24 v25 v26
                             -> coe
                                  du_fsig'45'at_1868 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                                  (coe v25) (coe v26) (coe v19)
                                  (coe
                                     du_'60''45''8804'_808
                                     (coe du_sz'45'sigop_824 (coe v20) (coe v19))
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
                    MAlonzo.Code.Once.IR.C_const_126 v19 v20
                      -> coe
                           du_lit_2030 (coe v0) (coe v20)
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
             du_path_2056 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v9)
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
d_fsig'45'at_1868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fsig'45'at_1868 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 ~v12
                  ~v13 v14
  = du_fsig'45'at_1868 v0 v1 v2 v3 v7 v8 v9 v10 v11 v14
du_fsig'45'at_1868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fsig'45'at_1868 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v4 of
      MAlonzo.Code.Once.SigOp.Info.C_primV_90 v10
        -> case coe v10 of
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_222
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_1894 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_224
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_1894 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_226
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_1894 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_228
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v13 v14
                      -> coe
                           seq (coe v13)
                           (coe
                              seq (coe v14)
                              (coe
                                 seq (coe v6)
                                 (coe
                                    du_fbin'45'case_1894 (coe v0) (coe v1) (coe v2) (coe v3)
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
             MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_230
               -> coe
                    seq (coe v5)
                    (coe
                       seq (coe v6)
                       (coe
                          du_conv_2198 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
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
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.fbin-case
d_fbin'45'case_1894 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208 ->
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
d_fbin'45'case_1894 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12
                    ~v13 v14
  = du_fbin'45'case_1894 v0 v1 v2 v3 v5 v8 v9 v11 v14
du_fbin'45'case_1894 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'case_1894 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             seq (coe v9)
             (let v10
                    = coe
                        du_fbin'45'sound_1910 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
                                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                             (coe
                                                MAlonzo.Code.Once.Arith.Prim.du_primSem_238 v4 v0
                                                (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16))
                                                   (coe v11)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          erased))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound.fbin-sound
d_fbin'45'sound_1910 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_fbin'45'sound_1910 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10
  = du_fbin'45'sound_1910 v0 v1 v2 v3 v4 v5 v6 v10
du_fbin'45'sound_1910 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'sound_1910 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_fbin'45'at_1928 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         MAlonzo.Code.Once.Arith.Machine.Recognise.du_b'45'view_84 (coe v4)
         (coe v5))
      (coe v6) (coe v7)
-- Once.Adequacy.LiftSound.fbin-at
d_fbin'45'at_1928 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_fbin'45'at_1928 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_fbin'45'at_1928 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_fbin'45'at_1928 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.Recognise.T_BView_36 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fbin'45'at_1928 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Once.Arith.Machine.Recognise.C_bv'45'pair_48
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v19 v20
                      -> coe
                           du_pair_2328 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
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
                                  du_dist_2388 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
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
             du_ids_2468 (coe v8)
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
d_lit_2030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
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
d_lit_2030 v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_lit_2030 v0 v4 v10
du_lit_2030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lit_2030 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
            (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
            (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.Adequacy.LiftSound._.path
d_path_2056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_path_2056 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_path_2056 v0 v1 v3 v4 v5 v9 v10
du_path_2056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_path_2056 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_typed_2072 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v7)
             (coe
                MAlonzo.Code.Once.Arith.Machine.Shape.d_typePath'63'_160 (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NFloat_10) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._._.typed
d_typed_2072 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_typed_2072 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
             v14 ~v15 ~v16
  = du_typed_2072 v0 v1 v3 v4 v5 v9 v10 v14
du_typed_2072 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typed_2072 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (let v8
             = coe
                 du_path'45'ok_332 (coe v0) (coe v1)
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
d_conv_2198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
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
d_conv_2198 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 ~v13
  = du_conv_2198 v0 v1 v2 v3 v5 v6 v9 v10
du_conv_2198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conv_2198 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = coe
                     d_body'45'sound_1136 v0 v1 v2 v3
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                     v4 v5 v8 erased v6 in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> coe
                       seq (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
                             (coe
                                MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                (coe
                                   MAlonzo.Code.Once.Arith.Prim.du_primSem_238
                                   (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_230) v0
                                   (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
                                      (coe v10)))))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LiftSound._.pair
d_pair_2328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair_2328 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_pair_2328 v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 v15
du_pair_2328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_pair_2328 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
               -> let v14
                        = coe
                            d_fbody'45'sound_1828 v0 v1 v2 v3 v4 v6
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                               (coe
                                  du_sz_686
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                  (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                               (coe du_sz'45'pair'737'_840 (coe v4) (coe v6)) (coe v8))
                            v12 erased v9 in
                  coe
                    (let v15
                           = coe
                               d_fbody'45'sound_1828 v0 v1 v2 v3 v5 v7
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_686
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v4) (coe v5))
                                     (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7))
                                  (coe du_sz'45'pair'691'_856 (coe v5) (coe v7)) (coe v8))
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
d_dist_2388 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_dist_2388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19
  = du_dist_2388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v15
du_dist_2388 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_dist_2388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      seq (coe v12)
      (coe
         du_pair_2406 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
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
d_pair_2406 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_pair_2406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_pair_2406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v14 v19 v21
du_pair_2406 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
du_pair_2406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> case coe v13 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> let v16
                        = coe du_plumbing'45'val_148 (coe v4) (coe v9) (coe v11) in
                  coe
                    (let v17
                           = coe
                               d_fbody'45'sound_1828 v0 v1 v2 v3 v5
                               (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v7 v9)
                               (coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                  (coe
                                     du_sz_686
                                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                        (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                        v9))
                                  (coe
                                     du_sz'45'dist'737'_876 (coe v4) (coe v5) (coe v6) (coe v7)
                                     (coe v8) (coe v9))
                                  (coe v10))
                               v14 erased v11 in
                     coe
                       (let v18
                              = coe
                                  d_fbody'45'sound_1828 v0 v1 v2 v3 v6
                                  (coe MAlonzo.Code.Once.IR.C__'8728'__28 v4 v8 v9)
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                     (coe
                                        du_sz_686
                                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v5) (coe v6))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__28 v4
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v7 v8)
                                           v9))
                                     (coe
                                        du_sz'45'dist'691'_924 (coe v4) (coe v5) (coe v6) (coe v7)
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
d_ids_2468 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
d_ids_2468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 ~v13
           ~v14 ~v15
  = du_ids_2468 v8 v9 v11
du_ids_2468 ::
  AgdaAny ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ids_2468 v0 v1 v2
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
d_block'45'int_2494 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'int_2494 = erased
-- Once.Adequacy.LiftSound.block-flt
d_block'45'flt_2508 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'flt_2508 = erased
-- Once.Adequacy.LiftSound.just-int
d_just'45'int_2520 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'int_2520 = erased
-- Once.Adequacy.LiftSound.just-flt
d_just'45'flt_2526 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'flt_2526 = erased
-- Once.Adequacy.LiftSound.lift-sound
d_lift'45'sound_2538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'sound_2538 = erased
-- Once.Adequacy.LiftSound._.with-body
d_with'45'body_2628 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_with'45'body_2628 = erased
-- Once.Adequacy.LiftSound._.with-body
d_with'45'body_2728 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_with'45'body_2728 = erased
