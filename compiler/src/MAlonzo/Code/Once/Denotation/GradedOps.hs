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
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Denotation.GradedOps.fmapM
d_fmapM_12 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmapM_12 v0 ~v1 ~v2 v3 v4 = du_fmapM_12 v0 v3 v4
du_fmapM_12 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmapM_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30 -> coe v1 v2
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.injB
d_injB_24 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB_24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Void_12 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_injB_24 (coe v7) (coe v5) (coe v9))
                           (coe d_injB_24 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v7 v8
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
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_prjB_56 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Void_12 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_prjB_56 (coe v7) (coe v5) (coe v9))
                           (coe d_prjB_56 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v7 v8
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
-- Once.Denotation.GradedOps.cfᵛ
d_cf'7515'_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'7515'_90 v0 ~v1 v2 v3 = du_cf'7515'_90 v0 v2 v3
du_cf'7515'_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'7515'_90 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v5
               -> coe d_prjB_56 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'7515'_90 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'7515'_90 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'7515'_90 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'7515'_90 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.cf⁻¹ᵛ
d_cf'8315''185''7515'_132 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_cf'8315''185''7515'_132 v0 ~v1 v2 v3
  = du_cf'8315''185''7515'_132 v0 v2 v3
du_cf'8315''185''7515'_132 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_cf'8315''185''7515'_132 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v5
               -> coe d_injB_24 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_cf'8315''185''7515'_132 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_cf'8315''185''7515'_132 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_cf'8315''185''7515'_132 (coe v7) (coe v5) (coe v9))
                           (coe du_cf'8315''185''7515'_132 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.seqM
d_seqM_176 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_seqM_176 v0 v1 ~v2 v3 = du_seqM_176 v0 v1 v3
du_seqM_176 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 -> AgdaAny -> AgdaAny
du_seqM_176 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30 -> coe v2
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe
             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.in-valueᵛ
d_in'45'value'7515'_188 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_in'45'value'7515'_188 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_1060 (coe v0)
      (coe du_cf'7515'_90 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.GradedOps.cata-semᵛ
d_cata'45'sem'7515'_202 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_cata'45'sem'7515'_202 v0 v1 ~v2 v3 v4
  = du_cata'45'sem'7515'_202 v0 v1 v3 v4
du_cata'45'sem'7515'_202 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_cata'45'sem'7515'_202 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080 (coe v1)
      (coe v2)
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_28 (coe v0)
              (coe du_seqM_176 (coe v0) (coe v1) (coe v4))
              (coe
                 (\ v5 ->
                    coe
                      v3 (coe du_cf'8315''185''7515'_132 (coe v1) (coe v2) (coe v5))))))
-- Once.Denotation.GradedOps.anaᵖ
d_ana'7510'_222 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_74
d_ana'7510'_222 v0 ~v1 v2 v3 = du_ana'7510'_222 v0 v2 v3
du_ana'7510'_222 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_74
du_ana'7510'_222 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.GradedDomain.C_constructor_82
      (coe du_mapAna'7510'_230 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Denotation.GradedOps.mapAnaᵖ
d_mapAna'7510'_230 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapAna'7510'_230 v0 v1 ~v2 v3 v4
  = du_mapAna'7510'_230 v0 v1 v3 v4
du_mapAna'7510'_230 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapAna'7510'_230 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_ana'7510'_222 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7510'_230 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7510'_230 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7510'_230 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7510'_230 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.embν
d_embν_286 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_74 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
d_embν_286 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.C_constructor_16
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182
         (coe
            d_mapEmbν_292 (coe v0) (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.GradedDomain.d_force'7510'_80
               (coe v1))))
-- Once.Denotation.GradedOps.mapEmbν
d_mapEmbν_292 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapEmbν_292 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_embν_286 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapEmbν_292 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapEmbν_292 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapEmbν_292 (coe v0) (coe v3) (coe v5))
                    (coe d_mapEmbν_292 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.ana-semᵛ
d_ana'45'sem'7515'_342 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ana'45'sem'7515'_342 v0 ~v1 v2 v3 v4 v5 v6
  = du_ana'45'sem'7515'_342 v0 v2 v3 v4 v5 v6
du_ana'45'sem'7515'_342 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ana'45'sem'7515'_342 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> coe
             MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_28 (coe v2)
             (coe v4)
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_56 (coe v2)
                     (coe
                        du_ana'7510'_222
                        (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                                erased (coe du_cf'7515'_90 (coe v0) (coe v3) (coe v6 v7))))
                        (coe v5))))
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe
             MAlonzo.Code.Once.Denotation.GradedDomain.du_returnM_56 (coe v2)
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
                                erased (coe du_cf'7515'_90 (coe v0) (coe v3) (coe v7))))
                        (coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                           (coe
                              MAlonzo.Code.Once.Denotation.GradedDomain.du_toT_66 (coe v2)
                              (coe v4))
                           (coe (\ v7 -> coe v7 v6)))))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.out-semᵛ
d_out'45'sem'7515'_382 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
d_out'45'sem'7515'_382 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> coe
             du_cf'8315''185''7515'_132 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126 v1 v2
                erased
                (MAlonzo.Code.Once.Denotation.GradedDomain.d_force'7510'_80
                   (coe v3)))
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
             (coe
                (\ v4 ->
                   coe
                     du_cf'8315''185''7515'_132 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'out_1126 v1 v2
                        erased v4)))
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.d_force'7496'_14 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.⟦_⟧<:ᵛ
d_'10214'_'10215''60''58''7515'_402 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215''60''58''7515'_402 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'unit_26 -> coe v3
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'int_28 -> coe v3
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'float_30 -> coe v3
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'arr_46 v11 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_44
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_402 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe v3 v22)))
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_44
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_402 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_402
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
                                    -> coe
                                         (\ v22 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.GradedDomain.du_subM_44
                                              (coe v13)
                                              (coe
                                                 du_fmapM_12 (coe v18)
                                                 (coe
                                                    d_'10214'_'10215''60''58''7515'_402 (coe v16)
                                                    (coe v21) (coe v12))
                                                 (coe
                                                    v3
                                                    (d_'10214'_'10215''60''58''7515'_402
                                                       (coe v19) (coe v14) (coe v11) (coe v22)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'prod_56 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__24 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_402 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_402 (coe v11) (coe v13)
                                     (coe v9) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'sum_66 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__26 v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_402 (coe v10) (coe v12)
                                     (coe v8) (coe v14))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_'10214'_'10215''60''58''7515'_402 (coe v11) (coe v13)
                                     (coe v9) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'μ_70 -> coe v3
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'ν_78 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Type.Sub.C_'8849''45'pure_10 -> coe v3
                    MAlonzo.Code.Once.Spec.Type.Sub.C_'8849''45'eff_12 -> coe v3
                    MAlonzo.Code.Once.Spec.Type.Sub.C_'8849''45'pe_14
                      -> coe
                           d_embν_286
                           (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v8))
                           (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Sub.C_sub'45'rigid_84 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GradedOps.sigOpRefᵛ
d_sigOpRef'7515'_482 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_sigOpRef'7515'_482 v0 v1 v2 v3 v4 v5 ~v6
  = du_sigOpRef'7515'_482 v0 v1 v2 v3 v4 v5
du_sigOpRef'7515'_482 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 -> AgdaAny
du_sigOpRef'7515'_482 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_con'45'base_38 v7
        -> coe
             d_injB_24 (coe v0) (coe v7)
             (coe
                MAlonzo.Code.Once.Spec.Contract.du_valueOf_340 v2 v3
                (coe
                   MAlonzo.Code.Once.Spec.Contract.C_key_138
                   (coe MAlonzo.Code.Once.Spec.Name.d_showCanonical_44 (coe v4))
                   (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20) (coe v0))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_con'45'fun_46 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v14 v15
                      -> case coe v14 of
                           MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_340 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Name.d_showCanonical_44
                                                       (coe v4))
                                                    (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20)
                                                    (coe v13))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                              (coe d_injB_24 (coe v13) (coe v10))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106
                                                 v1
                                                 (MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_324
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_260
                                                       (coe v2) (coe v3)))
                                                 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20) v13
                                                 (coe
                                                    MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                    (coe v13) (coe v12) (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10)
                                                    (coe v10))
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_340 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Name.d_showCanonical_44
                                                       (coe v4))
                                                    (coe v11) (coe v13))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                              (coe d_injB_24 (coe v13) (coe v10))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106
                                                 v1
                                                 (MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_324
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_260
                                                       (coe v2) (coe v3)))
                                                 v11 v13
                                                 (coe
                                                    MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                    (coe v13) (coe v12) (coe v4) (coe v9) (coe v10))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
                                    -> coe
                                         (\ v16 ->
                                            d_injB_24
                                              (coe v13) (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Contract.du_valueOf_340 v2
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Contract.C_key_138
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Name.d_showCanonical_44
                                                       (coe v4))
                                                    (coe v11) (coe v13))
                                                 (d_prjB_56 (coe v11) (coe v9) (coe v16))))
                                  MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
                                    -> coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                              (coe d_injB_24 (coe v13) (coe v10))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106
                                                 v1
                                                 (MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_324
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_260
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
