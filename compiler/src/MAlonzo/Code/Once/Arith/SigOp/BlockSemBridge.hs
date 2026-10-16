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

module MAlonzo.Code.Once.Arith.SigOp.BlockSemBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Machine.WordSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.BlockSemBridge.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_440
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_12
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_408
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor
d_coerce'45'functor_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_14 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-in
d_coerce'45'μ'45'in_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_18 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 v0 v2
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-μ-out
d_coerce'45'μ'45'out_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_20 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 v0 v1 v3
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-in
d_coerce'45'ν'45'in_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614
-- Once.Arith.SigOp.BlockSemBridge.M.coerce-ν-out
d_coerce'45'ν'45'out_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_24
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620
-- Once.Arith.SigOp.BlockSemBridge.M.eraseᵍ
d_erase'7501'_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_26
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoIn
d_sem'45'CoIn_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_634
-- Once.Arith.SigOp.BlockSemBridge.M.sem-CoOut
d_sem'45'CoOut_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_30
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_624
-- Once.Arith.SigOp.BlockSemBridge.M.sem-In
d_sem'45'In_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_32 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Arith.SigOp.BlockSemBridge.M.sem-Out
d_sem'45'Out_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_34
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_562
-- Once.Arith.SigOp.BlockSemBridge.M.sem-ana
d_sem'45'ana_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_644 v0 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-cata
d_sem'45'cata_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_38 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sem-fmap
d_sem'45'fmap_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.sem-para
d_sem'45'para_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_42 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_590 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.semAnaLayer
d_semAnaLayer_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_44 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_650 v0 v2 v3
-- Once.Arith.SigOp.BlockSemBridge.M.sfmapSemAna
d_sfmapSemAna_46 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_46 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_658 v0 v1 v3 v4
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧
d_'10214'_'10215'_48 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_48 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧F
d_'10214'_'10215'F_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_50 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_52 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦μ⟧
d_'10214'μ'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_54 = erased
-- Once.Arith.SigOp.BlockSemBridge.M.⟦ν⟧
d_'10214'ν'10215'_56 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_56 = erased
-- Once.Arith.SigOp.BlockSemBridge._._.eval-arith-W
d_eval'45'arith'45'W_66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_66 v0
  = coe
      MAlonzo.Code.Once.Arith.Machine.WordSem.d_eval'45'arith'45'W_38
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.F
d_F_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_F_68 v0
  = coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0)
-- Once.Arith.SigOp.BlockSemBridge._.W._%ˢ_
d__'37''738'__72 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__72 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._/ˢ_
d__'47''738'__74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__74 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._<ˢ_
d__'60''738'__76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__76 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._divℕ_
d__divℕ__78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__78 ~v0 = du__divℕ__78
du__divℕ__78 :: Integer -> Integer -> Integer
du__divℕ__78 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Arith.SigOp.BlockSemBridge._.W._modℕ_
d__modℕ__80 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__80 ~v0 = du__modℕ__80
du__modℕ__80 :: Integer -> Integer -> Integer
du__modℕ__80 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Arith.SigOp.BlockSemBridge._.W._≡ʷ_
d__'8801''695'__82 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__82 ~v0 = du__'8801''695'__82
du__'8801''695'__82 :: Integer -> Integer -> Bool
du__'8801''695'__82
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Arith.SigOp.BlockSemBridge._.W._⊕_
d__'8853'__84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__84 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._⊖_
d__'8854'__86 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__86 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W._⊗_
d__'8855'__88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__88 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.InRange
d_InRange_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_90 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.Word
d_Word_92 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_92 = erased
-- Once.Arith.SigOp.BlockSemBridge._.W.fromℤ
d_fromℤ_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_94 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.half
d_half_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_96 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.inRange?
d_inRange'63'_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_98 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.intMin
d_intMin_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_100 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.modulus
d_modulus_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_102 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.modulus≢0
d_modulus'8802'0_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_104 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.negOne
d_negOne_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_106 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.norm
d_norm_108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_108 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.tdivℤ
d_tdivℤ_110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_110 ~v0 = du_tdivℤ_110
du_tdivℤ_110 :: Integer -> Integer -> Integer
du_tdivℤ_110 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Arith.SigOp.BlockSemBridge._.W.tmodℤ
d_tmodℤ_112 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_112 ~v0 = du_tmodℤ_112
du_tmodℤ_112 :: Integer -> Integer -> Integer
du_tmodℤ_112 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Arith.SigOp.BlockSemBridge._.W.toWord
d_toWord_114 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Arith.SigOp.BlockSemBridge._.W.toℤ
d_toℤ_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_116 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.W.⊝_
d_'8861'__118 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__118 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.%ˢ-else
d_'37''738''45'else_122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'else_122 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.%ˢ-in-range
d_'37''738''45'in'45'range_124 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'37''738''45'in'45'range_124 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Word.du_'37''738''45'in'45'range_530
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v3
      v4 v5
-- Once.Arith.SigOp.BlockSemBridge._.WL.%ˢ-mid
d_'37''738''45'mid_126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'mid_126 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.%ˢ-negOne
d_'37''738''45'negOne_128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'negOne_128 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.%ˢ-zero
d_'37''738''45'zero_130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''738''45'zero_130 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-else
d_'47''738''45'else_132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'else_132 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-in-range
d_'47''738''45'in'45'range_134 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''738''45'in'45'range_134 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_'47''738''45'in'45'range_496
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v3
      v4
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-mid
d_'47''738''45'mid_136 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'mid_136 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-negOne
d_'47''738''45'negOne_138 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'negOne_138 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-pow2
d_'47''738''45'pow2_140 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'pow2_140 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL./ˢ-zero
d_'47''738''45'zero_142 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''738''45'zero_142 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.0<half
d_0'60'half_144 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'half_144 ~v0 = du_0'60'half_144
du_0'60'half_144 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'half_144 = coe MAlonzo.Code.Once.Word.du_0'60'half_100
-- Once.Arith.SigOp.BlockSemBridge._.WL.0<modulus
d_0'60'modulus_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'modulus_146 ~v0 = du_0'60'modulus_146
du_0'60'modulus_146 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'modulus_146 = coe MAlonzo.Code.Once.Word.du_0'60'modulus_98
-- Once.Arith.SigOp.BlockSemBridge._.WL.0<negOne
d_0'60'negOne_148 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'negOne_148 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_0'60'negOne_352
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.1<modulus
d_1'60'modulus_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'60'modulus_150 v0
  = coe
      MAlonzo.Code.Once.Word.d_1'60'modulus_722
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.2*n≡n+n
d_2'42'n'8801'n'43'n_152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'n'8801'n'43'n_152 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.2≤modulus
d_2'8804'modulus_154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_2'8804'modulus_154 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_2'8804'modulus_348
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.<⇒<ᵇtrue
d_'60''8658''60''7495'true_156 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8658''60''7495'true_156 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.fromℤ-0
d_fromℤ'45'0_158 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'0_158 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.fromℤ-in-range
d_fromℤ'45'in'45'range_160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℤ'45'in'45'range_160 v0
  = coe
      MAlonzo.Code.Once.Word.d_fromℤ'45'in'45'range_106
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.fromℤ-neg-toℤ
d_fromℤ'45'neg'45'toℤ_162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg'45'toℤ_162 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.fromℤ-neg1
d_fromℤ'45'neg1_164 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℤ'45'neg1_164 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.half<modulus
d_half'60'modulus_166 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'60'modulus_166 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'60'modulus_356
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.half≡2^b
d_half'8801'2'94'b_168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_half'8801'2'94'b_168 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.half≤negOne
d_half'8804'negOne_170 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_half'8804'negOne_170 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_half'8804'negOne_376
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.lit-hi
d_lit'45'hi_172 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'hi_172 ~v0 = du_lit'45'hi_172
du_lit'45'hi_172 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lit'45'hi_172 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Word.du_lit'45'hi_580 v3
-- Once.Arith.SigOp.BlockSemBridge._.WL.lit-lo
d_lit'45'lo_174 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'lo_174 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Word.du_lit'45'lo_592
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v3
      v4
-- Once.Arith.SigOp.BlockSemBridge._.WL.modulus∸negOne≡1
d_modulus'8760'negOne'8801'1_176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_modulus'8760'negOne'8801'1_176 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.mod∸half≡half
d_mod'8760'half'8801'half_178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8760'half'8801'half_178 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.mod≡half+half
d_mod'8801'half'43'half_180 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8801'half'43'half_180 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.negOne<modulus
d_negOne'60'modulus_182 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_negOne'60'modulus_182 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Word.du_negOne'60'modulus_364
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.negOne≢0
d_negOne'8802'0_184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_negOne'8802'0_184 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.norm-0
d_norm'45'0_186 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'0_186 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.norm-id
d_norm'45'id_188 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_norm'45'id_188 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.sbb-pos
d_sbb'45'pos_190 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'pos_190 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.sbb-zero
d_sbb'45'zero_192 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sbb'45'zero_192 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.sdiv2ᵏ
d_sdiv2'7503'_194 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_sdiv2'7503'_194 v0
  = coe
      MAlonzo.Code.Once.Word.d_sdiv2'7503'_70
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.shlᵂ
d_shl'7490'_196 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_shl'7490'_196 v0
  = coe
      MAlonzo.Code.Once.Word.d_shl'7490'_64
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.BlockSemBridge._.WL.sucNegOne≡mod
d_sucNegOne'8801'mod_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sucNegOne'8801'mod_198 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.tdiv-neg1
d_tdiv'45'neg1_200 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tdiv'45'neg1_200 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.tmod-neg1
d_tmod'45'neg1_202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tmod'45'neg1_202 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.toWord≡fromℤ
d_toWord'8801'fromℤ_204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'8801'fromℤ_204 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.toℤ-negOne
d_toℤ'45'negOne_206 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'45'negOne_206 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.toℤ∘fromℤ
d_toℤ'8728'fromℤ_208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℤ'8728'fromℤ_208 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.unplus
d_unplus_210 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_unplus_210 ~v0 = du_unplus_210
du_unplus_210 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_unplus_210 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Word.du_unplus_574 v4
-- Once.Arith.SigOp.BlockSemBridge._.WL.≡ᵇ0-false
d_'8801''7495'0'45'false_212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495'0'45'false_212 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.≤⇒<ᵇfalse
d_'8804''8658''60''7495'false_214 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8658''60''7495'false_214 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊕-neg
d_'8853''45'neg_216 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg_216 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊕-neg-suc
d_'8853''45'neg'45'suc_218 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'neg'45'suc_218 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊕-normʳ
d_'8853''45'norm'691'_220 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''45'norm'691'_220 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊕≡+
d_'8853''8801''43'_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8853''8801''43'_222 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊖-normʳ
d_'8854''45'norm'691'_224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'norm'691'_224 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊖-self
d_'8854''45'self_226 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'self_226 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊖≡∸
d_'8854''8801''8760'_228 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''8801''8760'_228 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊗-pow2
d_'8855''45'pow2_230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8855''45'pow2_230 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊝-fromℤ
d_'8861''45'fromℤ_232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'fromℤ_232 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊝-intMin
d_'8861''45'intMin_234 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'intMin_234 = erased
-- Once.Arith.SigOp.BlockSemBridge._.WL.⊝-invol-norm
d_'8861''45'invol'45'norm_236 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8861''45'invol'45'norm_236 = erased
-- Once.Arith.SigOp.BlockSemBridge._.toWord
d_toWord_240 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> AgdaAny
d_toWord_240 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'unit_10
        -> coe seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'int_12
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2)
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'float_14 -> coe v2
      MAlonzo.Code.Once.Arith.Machine.Shape.C_shape'45'pair_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_toWord_240 (coe v0) (coe v3) (coe v5))
                    (coe d_toWord_240 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.BlockSemBridge._.project-commute
d_project'45'commute_260 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_project'45'commute_260 = erased
-- Once.Arith.SigOp.BlockSemBridge._.projectF-commute
d_projectF'45'commute_308 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectF'45'commute_308 = erased
-- Once.Arith.SigOp.BlockSemBridge._.readLeaf-commute
d_readLeaf'45'commute_356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLeaf'45'commute_356 = erased
-- Once.Arith.SigOp.BlockSemBridge._.readLeafF-commute
d_readLeafF'45'commute_378 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLeafF'45'commute_378 = erased
-- Once.Arith.SigOp.BlockSemBridge._.eval≡semM
d_eval'8801'semM_402 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'8801'semM_402 = erased
