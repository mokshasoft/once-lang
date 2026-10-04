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

module MAlonzo.Code.Once.Denotation.GradedOps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Denotation.GradedOps.fmapM
d_fmapM_12 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmapM_12 v0 ~v1 ~v2 v3 v4 = du_fmapM_12 v0 v3 v4
du_fmapM_12 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmapM_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34 -> coe v1 v2
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.injB
d_injB_24 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_injB_24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_injB_24 (coe v7) (coe v5) (coe v9))
                           (coe d_injB_24 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_injB_24 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_injB_24 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.prjB
d_prjB_56 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_prjB_56 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_prjB_56 (coe v7) (coe v5) (coe v9))
                           (coe d_prjB_56 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_prjB_56 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_prjB_56 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.injBᵍ
d_injB'7501'_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_injB'7501'_88 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_injB'7501'_88 (coe v7) (coe v5) (coe v9))
                           (coe d_injB'7501'_88 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_injB'7501'_88 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_injB'7501'_88 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.cfᵛ
d_cf'7515'_122 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
d_cf'7515'_122 v0 ~v1 v2 v3 = du_cf'7515'_122 v0 v2 v3
du_cf'7515'_122 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_cf'7515'_122 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe d_prjB_56 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'7515'_122 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'7515'_122 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'7515'_122 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'7515'_122 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.cf⁻¹ᵛ
d_cf'8315''185''7515'_164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
d_cf'8315''185''7515'_164 v0 ~v1 v2 v3
  = du_cf'8315''185''7515'_164 v0 v2 v3
du_cf'8315''185''7515'_164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_cf'8315''185''7515'_164 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe d_injB_24 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'8315''185''7515'_164 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'8315''185''7515'_164 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'8315''185''7515'_164 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'8315''185''7515'_164 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.seqM
d_seqM_208 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_seqM_208 v0 v1 ~v2 v3 = du_seqM_208 v0 v1 v3
du_seqM_208 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_seqM_208 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34 -> coe v2
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.in-valueᵛ
d_in'45'value'7515'_220 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_in'45'value'7515'_220 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060 (coe v0)
      (coe du_cf'7515'_122 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.GradedOps.cata-semᵛ
d_cata'45'sem'7515'_234 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_cata'45'sem'7515'_234 v0 v1 ~v2 v3 v4
  = du_cata'45'sem'7515'_234 v0 v1 v3 v4
du_cata'45'sem'7515'_234 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_cata'45'sem'7515'_234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 (coe v1)
      (coe v2)
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v0)
              (coe du_seqM_208 (coe v0) (coe v1) (coe v4))
              (coe
                 (\ v5 ->
                    coe
                      v3 (coe du_cf'8315''185''7515'_164 (coe v1) (coe v2) (coe v5))))))
-- Once.Denotation.GradedOps.anaᵖ
d_ana'7510'_254 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_140
d_ana'7510'_254 v0 ~v1 v2 v3 = du_ana'7510'_254 v0 v2 v3
du_ana'7510'_254 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_140
du_ana'7510'_254 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.GradedDomain.C_constructor_148
      (coe du_mapAna'7510'_262 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Denotation.GradedOps.mapAnaᵖ
d_mapAna'7510'_262 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapAna'7510'_262 v0 v1 ~v2 v3 v4
  = du_mapAna'7510'_262 v0 v1 v3 v4
du_mapAna'7510'_262 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapAna'7510'_262 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_ana'7510'_254 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7510'_262 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7510'_262 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7510'_262 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7510'_262 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.embν
d_embν_318 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_140 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
d_embν_318 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.C_constructor_16
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182
         (coe
            d_mapEmbν_324 (coe v0) (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.GradedDomain.d_force'7510'_146
               (coe v1))))
-- Once.Denotation.GradedOps.mapEmbν
d_mapEmbν_324 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν_324 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_embν_318 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν_324 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν_324 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν_324 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν_324 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.ana-semᵛ
d_ana'45'sem'7515'_374 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ana'45'sem'7515'_374 v0 ~v1 v2 v3 v4 v5 v6
  = du_ana'45'sem'7515'_374 v0 v2 v3 v4 v5 v6
du_ana'45'sem'7515'_374 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ana'45'sem'7515'_374 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_74 (coe v2)
             (coe v4)
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102 (coe v2)
                     (coe
                        du_ana'7510'_254
                        (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                                erased (coe du_cf'7515'_122 (coe v0) (coe v3) (coe v6 v7))))
                        (coe v5))))
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_102 (coe v2)
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.du_ana'7496'_64
                (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
                (coe
                   (\ v6 ->
                      coe
                        MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                                erased (coe du_cf'7515'_122 (coe v0) (coe v3) (coe v7))))
                        (coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                           (coe
                              MAlonzo.Code.Once.Denotation.GradedDomain.du_toT_132 (coe v2)
                              (coe v4))
                           (coe (\ v7 -> coe v7 v6)))))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.out-semᵛ
d_out'45'sem'7515'_414 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
d_out'45'sem'7515'_414 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             du_cf'8315''185''7515'_164 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126 v1 v2
                erased
                (MAlonzo.Code.Once.Denotation.GradedDomain.d_force'7510'_146
                   (coe v3)))
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_164 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126 v1 v2
                        erased v4)))
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.d_force'7496'_14 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.⟦_⟧<:ᵛ
d_'10214'_'10215''60''58''7515'_434 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 -> AgdaAny -> AgdaAny
d_'10214'_'10215''60''58''7515'_434 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_90
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_434 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe v3 v22)))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_90
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_434 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_434
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_90
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_434 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_434
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_434 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_434 (coe v11) (coe v13)
                                     (coe v9) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_434 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_434 (coe v11) (coe v13)
                                     (coe v9) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98 -> coe v3
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.Sub.C_'8849''45'pure_8 -> coe v3
                    MAlonzo.Code.Once.Type.Sub.C_'8849''45'eff_10 -> coe v3
                    MAlonzo.Code.Once.Type.Sub.C_'8849''45'pe_12
                      -> coe
                           d_embν_318
                           (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v8))
                           (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'rigid_112 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.sigOpRefᵛ
d_sigOpRef'7515'_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOpRef'7515'_514 v0 v1 v2 v3 v4 v5 ~v6
  = du_sigOpRef'7515'_514 v0 v1 v2 v3 v4 v5
du_sigOpRef'7515'_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 -> AgdaAny
du_sigOpRef'7515'_514 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v7
        -> coe
             d_injB_24 (coe v0) (coe v7)
             (coe
                MAlonzo.Code.Once.Spec.Contract.du_valueOf_456 v2 v3
                (coe
                   MAlonzo.Code.Once.Spec.Contract.C_key_138
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v4))
                   (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_456 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                                                       (coe v4))
                                                    (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                    (coe v13))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                              (d_injB_24
                                                 (coe v13) (coe v10)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.du_valueOf_456
                                                    v2 v3
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                       (coe
                                                          MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                                                          (coe v4))
                                                       (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                       (coe v13))
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_One_8
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_456 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                                                       (coe v4))
                                                    (coe v11) (coe v13))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                              (coe d_injB_24 (coe v13) (coe v10))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106
                                                 v1
                                                 (MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468
                                                       (coe v2) (coe v3)))
                                                 v11 v13
                                                 (coe
                                                    MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                    (coe v13) (coe v12) (coe v4) (coe v9) (coe v10))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_456 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                                                       (coe v4))
                                                    (coe v11) (coe v13))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                              (coe d_injB_24 (coe v13) (coe v10))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106
                                                 v1
                                                 (MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468
                                                       (coe v2) (coe v3)))
                                                 v11 v13
                                                 (coe
                                                    MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                    (coe v13) (coe v12) (coe v4) (coe v9) (coe v10))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
