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

module MAlonzo.Code.Once.Arith.Prim where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Bool
import qualified MAlonzo.Code.Once.Spec.Float.Arith
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Prim.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Arith.Prim.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Arith.Prim.M.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_246 v0 v2
-- Once.Arith.Prim.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_288
      v0 v2
-- Once.Arith.Prim.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Arith.Prim.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Arith.Prim.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578
-- Once.Arith.Prim.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
-- Once.Arith.Prim.M.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_104
-- Once.Arith.Prim.M.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_598
-- Once.Arith.Prim.M.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_588
-- Once.Arith.Prim.M.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_30
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_518
-- Once.Arith.Prim.M.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_526
-- Once.Arith.Prim.M.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Arith.Prim.M.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Arith.Prim.M.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Arith.Prim.M.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Arith.Prim.M.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Arith.Prim.M.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Arith.Prim.M.⟦_⟧
d_'10214'_'10215'_46 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Arith.Prim.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Arith.Prim.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Arith.Prim.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Arith.Prim.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Arith.Prim.W._%ˢ_
d__'37''738'__60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__60 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W._/ˢ_
d__'47''738'__62 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__62 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W._<ˢ_
d__'60''738'__64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__64 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W._divℕ_
d__divℕ__66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__66 ~v0 = du__divℕ__66
du__divℕ__66 :: Integer -> Integer -> Integer
du__divℕ__66 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Arith.Prim.W._modℕ_
d__modℕ__68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__68 ~v0 = du__modℕ__68
du__modℕ__68 :: Integer -> Integer -> Integer
du__modℕ__68 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Arith.Prim.W._≡ʷ_
d__'8801''695'__70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__70 ~v0 = du__'8801''695'__70
du__'8801''695'__70 :: Integer -> Integer -> Bool
du__'8801''695'__70
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Arith.Prim.W._⊕_
d__'8853'__72 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__72 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W._⊖_
d__'8854'__74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__74 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W._⊗_
d__'8855'__76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__76 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.InRange
d_InRange_78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_78 = erased
-- Once.Arith.Prim.W.Word
d_Word_80 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_80 = erased
-- Once.Arith.Prim.W.fromℤ
d_fromℤ_82 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_82 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.half
d_half_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_84 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.inRange?
d_inRange'63'_86 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_86 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.intMin
d_intMin_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_88 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.modulus
d_modulus_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_90 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.modulus≢0
d_modulus'8802'0_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_92 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.negOne
d_negOne_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_94 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.norm
d_norm_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_96 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.tdivℤ
d_tdivℤ_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_98 ~v0 = du_tdivℤ_98
du_tdivℤ_98 :: Integer -> Integer -> Integer
du_tdivℤ_98 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Arith.Prim.W.tmodℤ
d_tmodℤ_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_100 ~v0 = du_tmodℤ_100
du_tmodℤ_100 :: Integer -> Integer -> Integer
du_tmodℤ_100 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Arith.Prim.W.toWord
d_toWord_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Arith.Prim.W.toℤ
d_toℤ_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_104 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.W.⊝_
d_'8861'__106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__106 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.add-semM
d_add'45'semM_108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_add'45'semM_108 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8853'__28
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.sub-semM
d_sub'45'semM_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_sub'45'semM_116 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8854'__34
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.mul-semM
d_mul'45'semM_124 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mul'45'semM_124 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'8855'__40
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.neg-semM
d_neg'45'semM_132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_neg'45'semM_132 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
      (coe v1)
-- Once.Arith.Prim.fadd-semM
d_fadd'45'semM_138 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fadd'45'semM_138 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fadd_316
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.fsub-semM
d_fsub'45'semM_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fsub'45'semM_146 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fsub_318
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.fmul-semM
d_fmul'45'semM_154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fmul'45'semM_154 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fmul_320
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.fdiv-semM
d_fdiv'45'semM_162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_fdiv'45'semM_162 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Float.Arith.d_fdiv_322
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.i2f-semM
d_i2f'45'semM_170 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_i2f'45'semM_170 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Float.Arith.d_i2f_364
      (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Word.d_toℤ_52
         (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
         (coe v1))
-- Once.Arith.Prim.div-semM
d_div'45'semM_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_div'45'semM_176 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.mod-semM
d_mod'45'semM_184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_mod'45'semM_184 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.bool
d_bool_192 :: Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_bool_192 = coe MAlonzo.Code.Once.Spec.Bool.d_truth_6
-- Once.Arith.Prim.cmp-bool
d_cmp'45'bool_194 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer -> Integer -> Bool
d_cmp'45'bool_194 v0
  = coe
      MAlonzo.Code.Once.Arith.CmpOp.d_cmp'45'word_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.Prim.cmp-semM
d_cmp'45'semM_198 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cmp'45'semM_198 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe d_bool_192 (coe d_cmp'45'bool_194 v1 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Prim.ArithPrim
d_ArithPrim_208 a0 a1 = ()
data T_ArithPrim_208
  = C_p'45'add_210 | C_p'45'sub_212 | C_p'45'mul_214 |
    C_p'45'div_216 | C_p'45'mod_218 | C_p'45'neg_220 |
    C_p'45'fadd_222 | C_p'45'fsub_224 | C_p'45'fmul_226 |
    C_p'45'fdiv_228 | C_p'45'i2f_230 |
    C_p'45'cmp_232 MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6
-- Once.Arith.Prim.primSem
d_primSem_238 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T_ArithPrim_208 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
d_primSem_238 ~v0 ~v1 v2 = du_primSem_238 v2
du_primSem_238 ::
  T_ArithPrim_208 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
du_primSem_238 v0
  = case coe v0 of
      C_p'45'add_210 -> coe d_add'45'semM_108
      C_p'45'sub_212 -> coe d_sub'45'semM_116
      C_p'45'mul_214 -> coe d_mul'45'semM_124
      C_p'45'div_216 -> coe d_div'45'semM_176
      C_p'45'mod_218 -> coe d_mod'45'semM_184
      C_p'45'neg_220 -> coe d_neg'45'semM_132
      C_p'45'fadd_222 -> coe d_fadd'45'semM_138
      C_p'45'fsub_224 -> coe d_fsub'45'semM_146
      C_p'45'fmul_226 -> coe d_fmul'45'semM_154
      C_p'45'fdiv_228 -> coe d_fdiv'45'semM_162
      C_p'45'i2f_230 -> coe d_i2f'45'semM_170
      C_p'45'cmp_232 v1 -> coe d_cmp'45'semM_198 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
