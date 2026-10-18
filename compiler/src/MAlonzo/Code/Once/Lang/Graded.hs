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

module MAlonzo.Code.Once.Lang.Graded where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value

-- Once.Lang.Graded.Val.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Lang.Graded.Val.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Lang.Graded.Val.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Lang.Graded.Val.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Lang.Graded.Val.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Lang.Graded.Val.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Lang.Graded.Val.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.Graded.Val.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Lang.Graded.Val.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Lang.Graded.Val.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Lang.Graded.Val.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Lang.Graded.Val.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Lang.Graded.Val.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Lang.Graded.Val.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Lang.Graded.Val.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Lang.Graded.Val.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Lang.Graded.Val.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Lang.Graded.Val.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Lang.Graded.Val.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Lang.Graded.Val.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Lang.Graded.Val.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Lang.Graded.Val.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Lang.Graded.Val.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Lang.Graded.Val.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Lang.Graded.M
d_M_56 :: MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 -> () -> ()
d_M_56 = erased
-- Once.Lang.Graded._>>=ᵖ_
d__'62''62''61''7510'__68 ::
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61''7510'__68 ~v0 ~v1 v2 v3
  = du__'62''62''61''7510'__68 v2 v3
du__'62''62''61''7510'__68 ::
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61''7510'__68 v0 v1 = coe v1 v0
-- Once.Lang.Graded.bindM
d_bindM_80 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bindM_80 v0 ~v1 ~v2 v3 v4 = du_bindM_80 v0 v3 v4
du_bindM_80 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bindM_80 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe du__'62''62''61''7510'__68 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v1)
             (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Graded.subM
d_subM_100 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  () -> AgdaAny -> AgdaAny
d_subM_100 ~v0 ~v1 v2 ~v3 v4 = du_subM_100 v2 v4
du_subM_100 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> AgdaAny -> AgdaAny
du_subM_100 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16 -> coe v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v1
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Graded.returnM
d_returnM_118 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  () -> AgdaAny -> AgdaAny
d_returnM_118 ~v0 v1 ~v2 v3 = du_returnM_118 v1 v3
du_returnM_118 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> AgdaAny -> AgdaAny
du_returnM_118 v0 v1 = coe du_subM_100 (coe v0) (coe v1)
-- Once.Lang.Graded.EqM
d_EqM_128 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () -> AgdaAny -> AgdaAny -> ()
d_EqM_128 = erased
-- Once.Lang.Graded.toT∞
d_toT'8734'_146 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_toT'8734'_146 v0 ~v1 v2 = du_toT'8734'_146 v0 v2
du_toT'8734'_146 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
du_toT'8734'_146 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Graded.bindᵍ
d_bind'7501'_162 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bind'7501'_162 v0 v1 ~v2 ~v3 v4 v5
  = du_bind'7501'_162 v0 v1 v4 v5
du_bind'7501'_162 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bind'7501'_162 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe du__'62''62''61''7510'__68 (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe MAlonzo.Code.Once.Lang.Trace.du_fmapT_170 (coe v3) (coe v2)
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v2)
                    (coe v3)
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe
                    MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                    (coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v2))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
               -> coe
                    MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432 (coe v3)
                    (coe v2)
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
               -> coe
                    MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                    (coe v2)
                    (coe
                       (\ v4 ->
                          coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v3 v4)))
             MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
               -> coe
                    MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Graded.νᵖ
d_ν'7510'_198 a0 = ()
data T_ν'7510'_198 = C_constructor_206 AgdaAny
-- Once.Lang.Graded.νᵖ.forceᵖ
d_force'7510'_204 :: T_ν'7510'_198 -> AgdaAny
d_force'7510'_204 v0
  = case coe v0 of
      C_constructor_206 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Graded.⟦_⟧ᵛ
d_'10214'_'10215''7515'_208 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7515'_208 = erased
