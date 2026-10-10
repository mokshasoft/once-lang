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

module MAlonzo.Code.Once.Adequacy.GradedAnaBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.GradedOps
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueDomainLaws
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_
d__'8764''7510''7496'__10 a0 a1 a2 a3 = ()
-- Once.Adequacy.GradedAnaBridge._.RelGM
d_RelGM_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGM_14 = erased
-- Once.Adequacy.GradedAnaBridge._.RelGT
d_RelGT_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGT_16 = erased
-- Once.Adequacy.GradedAnaBridge._.RelGV
d_RelGV_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelGV_20 = erased
-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_26 ::
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_force'45''8764''7510''7496'_26 v0
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_force'45''8764''7510''7496'_24
      (coe v0)
-- Once.Adequacy.GradedAnaBridge.anaᵖ-∼
d_ana'7510''45''8764'_46 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
d_ana'7510''45''8764'_46 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_ana'7510''45''8764'_46 v0 v1 v5 v6 v7 v8 v9 v10
du_ana'7510''45''8764'_46 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
du_ana'7510''45''8764'_46 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.C_constructor_26
      (coe
         du_anaTree'7510'_66 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v2 v5) (coe v3 v6) (coe v4 v5 v6 v7))
-- Once.Adequacy.GradedAnaBridge.anaTreeᵖ
d_anaTree'7510'_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_anaTree'7510'_66 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaTree'7510'_66 v0 v1 v5 v6 v7 v8 v9 v10
du_anaTree'7510'_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_anaTree'7510'_66 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v11
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
                    (coe
                       du_mapAna'7510''45''8764'_88 (coe v0) (coe v1) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.mapAnaᵖ-∼
d_mapAna'7510''45''8764'_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7510''45''8764'_88 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
                            v11
  = du_mapAna'7510''45''8764'_88 v0 v1 v2 v6 v7 v8 v9 v10 v11
du_mapAna'7510''45''8764'_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7510''45''8764'_88 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v8
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             du_ana'7510''45''8764'_46 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           du_mapAna'7510''45''8764'_88 (coe v0) (coe v1) (coe v9) (coe v3)
                           (coe v4) (coe v5) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           du_mapAna'7510''45''8764'_88 (coe v0) (coe v1) (coe v10) (coe v3)
                           (coe v4) (coe v5) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_mapAna'7510''45''8764'_88 (coe v0) (coe v1) (coe v9)
                                     (coe v3) (coe v4) (coe v5) (coe v11) (coe v13) (coe v15))
                                  (coe
                                     du_mapAna'7510''45''8764'_88 (coe v0) (coe v1) (coe v10)
                                     (coe v3) (coe v4) (coe v5) (coe v12) (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-relᵍ
d_in'45'rel'7501'_174 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_in'45'rel'7501'_174 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_in'45'rel'7501'_174 v2 v3 v4 v5 v6
du_in'45'rel'7501'_174 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_in'45'rel'7501'_174 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v6 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_in'45'rel'7501'_174 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_in'45'rel'7501'_174 (coe v10) (coe v8) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_in'45'rel'7501'_174 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_in'45'rel'7501'_174 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-relᵍ-T
d_in'45'rel'7501''45'T_230 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_in'45'rel'7501''45'T_230 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 v8
  = du_in'45'rel'7501''45'T_230 v2 v3 v6 v7 v8
du_in'45'rel'7501''45'T_230 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_in'45'rel'7501''45'T_230 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_472
      (coe v2) (coe v3)
      (coe
         (\ v5 v6 v7 ->
            coe
              du_in'45'rel'7501'_174 (coe v0) (coe v1) (coe v5) (coe v6)
              (coe v7)))
      (coe v4)
-- Once.Adequacy.GradedAnaBridge.anaSD
d_anaSD_262 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
d_anaSD_262 ~v0 ~v1 v2 v3 ~v4 v5 = du_anaSD_262 v2 v3 v5
du_anaSD_262 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8
du_anaSD_262 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_anaF'7496'_264 (coe v0)
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
                 (coe v0) (coe v1))
              (coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                 (coe v2) (coe (\ v4 -> coe v4 v3)))))
-- Once.Adequacy.GradedAnaBridge.ana-bridgeᵍ
d_ana'45'bridge'7501'_296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_ana'45'bridge'7501'_296 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_ana'45'bridge'7501'_296 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_ana'45'bridge'7501'_296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_ana'45'bridge'7501'_296 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             du_retR_356 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
             (coe v8) (coe v9) (coe v10) (coe v2)
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             du_retR_422 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe v9) (coe v10) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.H
d_H_322 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
d_H_322 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_H_322 v3
du_H_322 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
du_H_322 v0
  = coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0)
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_330 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_cr_330 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13
  = du_cr_330 v3 v4 v5 v6 v7 v11 v12 v13
du_cr_330 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_cr_330 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_in'45'rel'7501''45'T_230 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 (coe v2 v5))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
         (coe v3) (coe (\ v8 -> coe v8 v6)))
      (coe
         du_kr_342 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.GradedAnaBridge._._.kr
d_kr_342 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_kr_342 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13
  = du_kr_342 v5 v6 v7 v11 v12 v13
du_kr_342 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_kr_342 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'bind_182
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v0)
      (coe v1) (coe v2) (coe (\ v6 v7 v8 -> coe v8 v3 v4 v5))
-- Once.Adequacy.GradedAnaBridge._.retR
d_retR_356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_retR_356 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_retR_356 v0 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_retR_356 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_retR_356 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      seq (coe v9)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
         (coe
            du_ana'7510''45''8764'_46 (coe v0) (coe du_H_322 (coe v1))
            (coe
               (\ v10 ->
                  coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v1
                    erased
                    (coe
                       MAlonzo.Code.Once.Denotation.GradedOps.du_cf'7515'_122 (coe v1)
                       (coe v2) (coe v3 v10))))
            (coe
               (\ v10 ->
                  coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v1
                       erased)
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
                          (coe v1) (coe v2))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                          (coe v4) (coe (\ v11 -> coe v11 v10))))))
            (coe du_cr_330 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
            (coe v6) (coe v7) (coe v8)))
-- Once.Adequacy.GradedAnaBridge._.H
d_H_388 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
d_H_388 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_H_388 v3
du_H_388 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6
du_H_388 v0
  = coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0)
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_398 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_cr_398 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13
  = du_cr_398 v3 v4 v5 v6 v7 v11 v12 v13
du_cr_398 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_cr_398 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_in'45'rel'7501''45'T_230 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
         (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v2)
         (coe (\ v8 -> coe v8 v5)))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
         (coe v3) (coe (\ v8 -> coe v8 v6)))
      (coe
         du_kr_410 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.GradedAnaBridge._._.kr
d_kr_410 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_kr_410 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13
  = du_kr_410 v5 v6 v7 v11 v12 v13
du_kr_410 ::
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_kr_410 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'bind_182
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v0)
      (coe v1) (coe v2) (coe (\ v6 v7 v8 -> coe v8 v3 v4 v5))
-- Once.Adequacy.GradedAnaBridge._.retR
d_retR_422 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_retR_422 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_retR_422 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_retR_422 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_retR_422 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      seq (coe v8)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomainLaws.du_ana'7496''45''8764'_152
            (coe du_H_388 (coe v0))
            (coe
               (\ v9 ->
                  coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                            erased
                            (coe
                               MAlonzo.Code.Once.Denotation.GradedOps.du_cf'7515'_122 (coe v0)
                               (coe v1) (coe v10))))
                    (coe v2 v9)))
            (coe
               (\ v9 ->
                  coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                       erased)
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
                          (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                          (coe v3) (coe (\ v10 -> coe v10 v9))))))
            (coe du_cr_398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
            (coe v5) (coe v6) (coe v7)))
