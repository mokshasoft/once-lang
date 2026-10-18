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

module MAlonzo.Code.Once.SigOp.Info where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.SigOp.Info.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.SigOp.Info.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.SigOp.Info.M.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.SigOp.Info.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.SigOp.Info.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.SigOp.Info.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.SigOp.Info.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.SigOp.Info.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.SigOp.Info.M.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.SigOp.Info.M.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.SigOp.Info.M.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.SigOp.Info.M.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.SigOp.Info.M.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.SigOp.Info.M.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.SigOp.Info.M.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.SigOp.Info.M.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.SigOp.Info.M.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.SigOp.Info.M.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.SigOp.Info.M.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.SigOp.Info.M.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.SigOp.Info.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.SigOp.Info.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.SigOp.Info.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.SigOp.Info.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.SigOp.Info.EffectShape
d_EffectShape_58 a0 = ()
data T_EffectShape_58
  = C_Pure_62 | C_Emits_64 | C_Halts_66 | C_Answers_68
-- Once.SigOp.Info.SigOpSem
d_SigOpSem_74 a0 a1 = ()
data T_SigOpSem_74
  = C_pureV_80 (MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
                AgdaAny -> AgdaAny) |
    C_ffiV_82 | C_callsV_84 | C_emitsV_86 | C_haltsV_88 |
    C_primV_90 MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208
-- Once.SigOp.Info.SigOpInfo
d_SigOpInfo_96 a0 a1 = ()
data T_SigOpInfo_96
  = C_mk'45'info''_118 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                       T_SigOpSem_74 MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
                       MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
-- Once.SigOp.Info.SigOpInfo.name
d_name_110 ::
  T_SigOpInfo_96 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_name_110 v0
  = case coe v0 of
      C_mk'45'info''_118 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.sem
d_sem_112 :: T_SigOpInfo_96 -> T_SigOpSem_74
d_sem_112 v0
  = case coe v0 of
      C_mk'45'info''_118 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.baseA
d_baseA_114 ::
  T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_baseA_114 v0
  = case coe v0 of
      C_mk'45'info''_118 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.conB
d_conB_116 ::
  T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_conB_116 v0
  = case coe v0 of
      C_mk'45'info''_118 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM-of
d_semM'45'of_124 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_SigOpSem_74 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semM'45'of_124 v0 v1 v2 v3 v4
  = case coe v4 of
      C_pureV_80 v5
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.Once.Lang.Res.C_returns_14
                  (coe
                     MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104 (coe v1)
                     (coe v5 v6 v7)))
      C_ffiV_82 -> coe (\ v5 -> coe v2 v3 v0 v1)
      C_callsV_84 -> coe (\ v5 -> coe v2 v3 v0 v1)
      C_emitsV_86
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.Once.Lang.Res.C_returns_14
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C_haltsV_88
        -> coe (\ v6 v7 -> coe MAlonzo.Code.Once.Lang.Res.C_stopped_12)
      C_primV_90 v5
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.Once.Lang.Res.C_returns_14
                  (coe
                     MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104 (coe v1)
                     (coe MAlonzo.Code.Once.Arith.Prim.du_primSem_238 v5 v6 v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.effect-of
d_effect'45'of_190 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpSem_74 -> T_EffectShape_58
d_effect'45'of_190 ~v0 ~v1 v2 = du_effect'45'of_190 v2
du_effect'45'of_190 :: T_SigOpSem_74 -> T_EffectShape_58
du_effect'45'of_190 v0
  = case coe v0 of
      C_pureV_80 v1 -> coe C_Pure_62
      C_ffiV_82 -> coe C_Pure_62
      C_callsV_84 -> coe C_Answers_68
      C_emitsV_86 -> coe C_Emits_64
      C_haltsV_88 -> coe C_Halts_66
      C_primV_90 v1 -> coe C_Pure_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM
d_semM_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  T_SigOpInfo_96 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semM_200 v0 v1 v2 v3
  = coe
      d_semM'45'of_124 (coe v0) (coe v1) (coe v2)
      (coe d_name_110 (coe v3)) (coe d_sem_112 (coe v3))
-- Once.SigOp.Info.effect
d_effect_210 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpInfo_96 -> T_EffectShape_58
d_effect_210 ~v0 ~v1 v2 = du_effect_210 v2
du_effect_210 :: T_SigOpInfo_96 -> T_EffectShape_58
du_effect_210 v0 = coe du_effect'45'of_190 (coe d_sem_112 (coe v0))
-- Once.SigOp.Info.Internal
d_Internal_218 a0 a1 a2 = ()
data T_Internal_218 = C_int'45'pure_226 | C_int'45'prim_230
-- Once.SigOp.Info.External
d_External_236 a0 a1 a2 = ()
data T_External_236
  = C_ext'45'ffi_242 | C_ext'45'calls_244 | C_ext'45'emits_248 |
    C_ext'45'halts_252
-- Once.SigOp.Info.sigop-owner
d_sigop'45'owner_260 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpSem_74 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sigop'45'owner_260 ~v0 ~v1 v2 = du_sigop'45'owner_260 v2
du_sigop'45'owner_260 ::
  T_SigOpSem_74 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sigop'45'owner_260 v0
  = case coe v0 of
      C_pureV_80 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_int'45'pure_226)
      C_ffiV_82
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'ffi_242)
      C_callsV_84
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'calls_244)
      C_emitsV_86
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'emits_248)
      C_haltsV_88
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'halts_252)
      C_primV_90 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_int'45'prim_230)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.internal-pure
d_internal'45'pure_268 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpSem_74 ->
  T_Internal_218 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_internal'45'pure_268 = erased
-- Once.SigOp.Info.semP
d_semP_276 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpInfo_96 ->
  T_Internal_218 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
d_semP_276 ~v0 ~v1 v2 = du_semP_276 v2
du_semP_276 ::
  T_SigOpInfo_96 ->
  T_Internal_218 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
du_semP_276 v0 = coe du_semP'45'of_290 (coe d_sem_112 (coe v0))
-- Once.SigOp.Info._.semP-of
d_semP'45'of_290 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_SigOpInfo_96 ->
  T_SigOpSem_74 ->
  T_Internal_218 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
d_semP'45'of_290 ~v0 ~v1 ~v2 v3 v4 = du_semP'45'of_290 v3 v4
du_semP'45'of_290 ::
  T_SigOpSem_74 ->
  T_Internal_218 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
du_semP'45'of_290 v0 v1
  = case coe v0 of
      C_pureV_80 v2 -> coe seq (coe v1) (coe v2)
      C_ffiV_82 -> coe (\ v2 v3 -> MAlonzo.RTE.mazUnreachableError)
      C_callsV_84 -> coe (\ v2 v3 -> MAlonzo.RTE.mazUnreachableError)
      C_emitsV_86 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C_haltsV_88 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C_primV_90 v2
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Once.Arith.Prim.du_primSem_238 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.mk-info
d_mk'45'info_300 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_58 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  T_SigOpInfo_96
d_mk'45'info_300 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_mk'45'info_300 v2 v3 v4 v5 v6
du_mk'45'info_300 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
   AgdaAny -> AgdaAny) ->
  T_EffectShape_58 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  T_SigOpInfo_96
du_mk'45'info_300 v0 v1 v2 v3 v4
  = case coe v2 of
      C_Pure_62
        -> coe
             C_mk'45'info''_118 (coe v0) (coe C_pureV_80 (coe v1)) (coe v3)
             (coe v4)
      C_Emits_64
        -> coe
             C_mk'45'info''_118 (coe v0) (coe C_emitsV_86) (coe v3) (coe v4)
      C_Halts_66
        -> coe
             C_mk'45'info''_118 (coe v0) (coe C_haltsV_88) (coe v3) (coe v4)
      C_Answers_68
        -> coe
             C_mk'45'info''_118 (coe v0) (coe C_callsV_84) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info._≟SigOpInfo-name_
d__'8799'SigOpInfo'45'name__346 ::
  T_SigOpInfo_96 ->
  T_SigOpInfo_96 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo'45'name__346 v0 v1
  = coe
      MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
      (coe d_name_110 (coe v0)) (coe d_name_110 (coe v1))
