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

module MAlonzo.Code.Once.Arith.SigOp.Builders where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.SigOp.Builders.W._%ˢ_
d__'37''738'__12 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'37''738'__12 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'37''738'__122
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._/ˢ_
d__'47''738'__14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'47''738'__14 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'47''738'__116
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._<ˢ_
d__'60''738'__16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'60''738'__16 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'60''738'__76
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._divℕ_
d__divℕ__18 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__divℕ__18 ~v0 = du__divℕ__18
du__divℕ__18 :: Integer -> Integer -> Integer
du__divℕ__18 = coe MAlonzo.Code.Once.Spec.Word.du__divℕ__88
-- Once.Arith.SigOp.Builders.W._modℕ_
d__modℕ__20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__modℕ__20 ~v0 = du__modℕ__20
du__modℕ__20 :: Integer -> Integer -> Integer
du__modℕ__20 = coe MAlonzo.Code.Once.Spec.Word.du__modℕ__90
-- Once.Arith.SigOp.Builders.W._≡ʷ_
d__'8801''695'__22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Bool
d__'8801''695'__22 ~v0 = du__'8801''695'__22
du__'8801''695'__22 :: Integer -> Integer -> Bool
du__'8801''695'__22
  = coe MAlonzo.Code.Once.Spec.Word.du__'8801''695'__82
-- Once.Arith.SigOp.Builders.W._⊕_
d__'8853'__24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8853'__24 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8853'__28
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊖_
d__'8854'__26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8854'__26 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8854'__34
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W._⊗_
d__'8855'__28 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d__'8855'__28 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d__'8855'__40
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.InRange
d_InRange_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> ()
d_InRange_30 = erased
-- Once.Arith.SigOp.Builders.W.Word
d_Word_32 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Word_32 = erased
-- Once.Arith.SigOp.Builders.W.fromℤ
d_fromℤ_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_fromℤ_34 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.half
d_half_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_half_36 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_half_50
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.inRange?
d_inRange'63'_38 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inRange'63'_38 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_inRange'63'_66
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.intMin
d_intMin_40 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_intMin_40 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_intMin_56
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.modulus
d_modulus_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_modulus_42 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.modulus≢0
d_modulus'8802'0_44 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_modulus'8802'0_44 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus'8802'0_14
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.negOne
d_negOne_46 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer
d_negOne_46 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_negOne_58
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.norm
d_norm_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_norm_48 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_norm_18
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.tdivℤ
d_tdivℤ_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tdivℤ_50 ~v0 = du_tdivℤ_50
du_tdivℤ_50 :: Integer -> Integer -> Integer
du_tdivℤ_50 = coe MAlonzo.Code.Once.Spec.Word.du_tdivℤ_104
-- Once.Arith.SigOp.Builders.W.tmodℤ
d_tmodℤ_52 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> Integer -> Integer
d_tmodℤ_52 ~v0 = du_tmodℤ_52
du_tmodℤ_52 :: Integer -> Integer -> Integer
du_tmodℤ_52 = coe MAlonzo.Code.Once.Spec.Word.du_tmodℤ_106
-- Once.Arith.SigOp.Builders.W.toWord
d_toWord_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_toWord_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Word.du_toWord_72
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0)) v1
-- Once.Arith.SigOp.Builders.W.toℤ
d_toℤ_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_toℤ_56 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_toℤ_52
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.W.⊝_
d_'8861'__58 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> Integer -> Integer
d_'8861'__58 v0
  = coe
      MAlonzo.Code.Once.Spec.Word.d_'8861'__46
      (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
-- Once.Arith.SigOp.Builders.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_62 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_62
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_440
-- Once.Arith.SigOp.Builders.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_64 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_64
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_408
-- Once.Arith.SigOp.Builders.M.coerce-functor
d_coerce'45'functor_66 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_66 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_68 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-in
d_coerce'45'μ'45'in_70 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_70 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 v0 v2
-- Once.Arith.SigOp.Builders.M.coerce-μ-out
d_coerce'45'μ'45'out_72 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.coerce-ν-in
d_coerce'45'ν'45'in_74 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_74
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614
-- Once.Arith.SigOp.Builders.M.coerce-ν-out
d_coerce'45'ν'45'out_76 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_76
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620
-- Once.Arith.SigOp.Builders.M.eraseᵍ
d_erase'7501'_78 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_78
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
-- Once.Arith.SigOp.Builders.M.sem-CoIn
d_sem'45'CoIn_80 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_80
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_634
-- Once.Arith.SigOp.Builders.M.sem-CoOut
d_sem'45'CoOut_82 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_82
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_624
-- Once.Arith.SigOp.Builders.M.sem-In
d_sem'45'In_84 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_84 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Arith.SigOp.Builders.M.sem-Out
d_sem'45'Out_86 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_86
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_562
-- Once.Arith.SigOp.Builders.M.sem-ana
d_sem'45'ana_88 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_88 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_644 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sem-cata
d_sem'45'cata_90 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_90 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Arith.SigOp.Builders.M.sem-fmap
d_sem'45'fmap_92 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_92 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
-- Once.Arith.SigOp.Builders.M.sem-para
d_sem'45'para_94 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_94 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_590 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.semAnaLayer
d_semAnaLayer_96 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_96 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_650 v0 v2 v3
-- Once.Arith.SigOp.Builders.M.sfmapSemAna
d_sfmapSemAna_98 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_98 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_658 v0 v1 v3 v4
-- Once.Arith.SigOp.Builders.M.⟦_⟧
d_'10214'_'10215'_100 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_100 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧F
d_'10214'_'10215'F_102 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_102 = erased
-- Once.Arith.SigOp.Builders.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_104 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_104 = erased
-- Once.Arith.SigOp.Builders.M.⟦μ⟧
d_'10214'μ'10215'_106 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_106 = erased
-- Once.Arith.SigOp.Builders.M.⟦ν⟧
d_'10214'ν'10215'_108 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_108 = erased
-- Once.Arith.SigOp.Builders.base-I×I
d_base'45'I'215'I_110 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_base'45'I'215'I_110
  = coe
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.base-U+U
d_base'45'U'43'U_112 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_base'45'U'43'U_112
  = coe
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
-- Once.Arith.SigOp.Builders.add-info
d_add'45'info_114 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_add'45'info_114
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.add.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'add_210))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.sub-info
d_sub'45'info_116 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_sub'45'info_116
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.sub.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'sub_212))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.mul-info
d_mul'45'info_118 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_mul'45'info_118
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mul.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mul_214))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.div-info
d_div'45'info_120 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_div'45'info_120
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.div.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'div_216))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.mod-info
d_mod'45'info_122 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_mod'45'info_122
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mod.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'mod_218))
      (coe d_base'45'I'215'I_110)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.neg-info
d_neg'45'info_124 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_neg'45'info_124
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.neg.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'neg_220))
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
-- Once.Arith.SigOp.Builders.base-F×F
d_base'45'F'215'F_126 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_base'45'F'215'F_126
  = coe
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.fadd-info
d_fadd'45'info_128 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_fadd'45'info_128
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.add.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fadd_222))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.fsub-info
d_fsub'45'info_130 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_fsub'45'info_130
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.sub.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fsub_224))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.fmul-info
d_fmul'45'info_132 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_fmul'45'info_132
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.mul.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fmul_226))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.fdiv-info
d_fdiv'45'info_134 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_fdiv'45'info_134
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.div.float" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'fdiv_228))
      (coe d_base'45'F'215'F_126)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.i2f-info
d_i2f'45'info_136 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_i2f'45'info_136
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.i2f" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe MAlonzo.Code.Once.Arith.Prim.C_p'45'i2f_230))
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)
      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)
-- Once.Arith.SigOp.Builders.lt-info
d_lt'45'info_138 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_lt'45'info_138
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.lt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'lt_8)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.le-info
d_le'45'info_140 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_le'45'info_140
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.le.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'le_10)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.gt-info
d_gt'45'info_142 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_gt'45'info_142
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.gt.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'gt_12)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.ge-info
d_ge'45'info_144 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ge'45'info_144
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.ge.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ge_14)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.eq-info
d_eq'45'info_146 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_eq'45'info_146
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.eq.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'eq_16)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.ne-info
d_ne'45'info_148 :: MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ne'45'info_148
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe ("arith.ne.int" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.SigOp.Info.C_primV_90
         (coe
            MAlonzo.Code.Once.Arith.Prim.C_p'45'cmp_232
            (coe MAlonzo.Code.Once.Arith.CmpOp.C_c'45'ne_18)))
      (coe d_base'45'I'215'I_110) (coe d_base'45'U'43'U_112)
-- Once.Arith.SigOp.Builders.value-info
d_value'45'info_154 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_value'45'info_154 ~v0 ~v1 v2 v3 v4
  = du_value'45'info_154 v2 v3 v4
du_value'45'info_154 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_value'45'info_154 v0 v1 v2
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_82) (coe v1) (coe v2)
-- Once.Arith.SigOp.Builders.generic-info
d_generic'45'info_166 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_generic'45'info_166 ~v0 ~v1 = du_generic'45'info_166
du_generic'45'info_166 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_generic'45'info_166 = coe du_value'45'info_154
-- Once.Arith.SigOp.Builders.arrow-sem-eff
d_arrow'45'sem'45'eff_172 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_arrow'45'sem'45'eff_172 ~v0 ~v1 v2 v3
  = du_arrow'45'sem'45'eff_172 v2 v3
du_arrow'45'sem'45'eff_172 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_arrow'45'sem'45'eff_172 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_88)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_86)
                              else coe
                                     seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_84)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-sem
d_arrow'45'sem_178 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_arrow'45'sem_178 ~v0 v1 v2 = du_arrow'45'sem_178 v1 v2
du_arrow'45'sem_178 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_arrow'45'sem_178 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_82
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe
                    du_arrow'45'sem'45'eff_172
                    (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v0))
                    (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v0))
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
               -> coe
                    du_arrow'45'sem'45'eff_172
                    (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v0))
                    (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v0))
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
               -> coe
                    du_arrow'45'sem'45'eff_172
                    (coe MAlonzo.Code.Once.Lang.Type.d_isVoid'63'_84 (coe v0))
                    (coe MAlonzo.Code.Once.Lang.Type.d_isUnit'63'_88 (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.SigOp.Builders.arrow-info
d_arrow'45'info_190 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_arrow'45'info_190 ~v0 v1 v2 v3 v4 v5
  = du_arrow'45'info_190 v1 v2 v3 v4 v5
du_arrow'45'info_190 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_arrow'45'info_190 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 (coe v2)
      (coe du_arrow'45'sem_178 (coe v0) (coe v1)) (coe v3) (coe v4)
