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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.GradedOps
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.StreamInf
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedAnaBridge._._∼ᵈ_
d__'8764''7496'__10 a0 a1 a2 a3 = ()
-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_
d__'8764''7510''7496'__14 a0 a1 a2 a3 = ()
-- Once.Adequacy.GradedAnaBridge._.RelGV
d_RelGV_22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_22 = erased
-- Once.Adequacy.GradedAnaBridge._._∼ᵈ_.force-∼
d_force'45''8764'_28 ::
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7496'__34 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_force'45''8764'_28 v0
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_force'45''8764'_44
      (coe v0)
-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_32 ::
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_force'45''8764''7510''7496'_32 v0
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_force'45''8764''7510''7496'_24
      (coe v0)
-- Once.Adequacy.GradedAnaBridge._._.anaᵖ-∼
d_ana'7510''45''8764'_64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
d_ana'7510''45''8764'_64 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_ana'7510''45''8764'_64 v0 v1 v5 v6 v7 v8 v9 v10
du_ana'7510''45''8764'_64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
du_ana'7510''45''8764'_64 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.C_constructor_26
      (coe
         du_anaRun'7510'_70 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v2 v5) (coe v3 v6) (coe v4 v5 v6 v7))
-- Once.Adequacy.GradedAnaBridge._._.anaRunᵖ
d_anaRun'7510'_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_anaRun'7510'_70 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaRun'7510'_70 v0 v1 v5 v6 v7 v8 v9 v10
du_anaRun'7510'_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_anaRun'7510'_70 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_anaBlock'7510'_76 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v6))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v7)))
-- Once.Adequacy.GradedAnaBridge._._.anaBlockᵖ
d_anaBlock'7510'_76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_anaBlock'7510'_76 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaBlock'7510'_76 v0 v1 v5 v6 v7 v8 v9 v10
du_anaBlock'7510'_76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_anaBlock'7510'_76 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                           (coe
                              du_mapAna'7510''45''8764'_84 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v4) (coe v1) (coe v5) (coe v12) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._._.mapAnaᵖ-∼
d_mapAna'7510''45''8764'_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7510''45''8764'_84 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                            v11
  = du_mapAna'7510''45''8764'_84 v0 v1 v5 v6 v7 v8 v9 v10 v11
du_mapAna'7510''45''8764'_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7510''45''8764'_84 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v8
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             du_ana'7510''45''8764'_64 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           du_mapAna'7510''45''8764'_84 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v9) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           du_mapAna'7510''45''8764'_84 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v10) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_mapAna'7510''45''8764'_84 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v9) (coe v11) (coe v13) (coe v15))
                                  (coe
                                     du_mapAna'7510''45''8764'_84 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v10) (coe v12) (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._._.anaᵈ-∼
d_ana'7496''45''8764'_144 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7496'__34
d_ana'7496''45''8764'_144 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_ana'7496''45''8764'_144 v0 v1 v5 v6 v7 v8 v9 v10
du_ana'7496''45''8764'_144 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7496'__34
du_ana'7496''45''8764'_144 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.C_constructor_46
      (coe
         du_anaRun'7496'_150 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v2 v5) (coe v3 v6) (coe v4 v5 v6 v7))
-- Once.Adequacy.GradedAnaBridge._._.anaRunᵈ
d_anaRun'7496'_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_anaRun'7496'_150 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaRun'7496'_150 v0 v1 v5 v6 v7 v8 v9 v10
du_anaRun'7496'_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_anaRun'7496'_150 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_anaBlock'7496'_156 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v6))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v7)))
-- Once.Adequacy.GradedAnaBridge._._.anaBlockᵈ
d_anaBlock'7496'_156 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_anaBlock'7496'_156 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaBlock'7496'_156 v0 v1 v5 v6 v7 v8 v9 v10
du_anaBlock'7496'_156 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_anaBlock'7496'_156 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
        -> case coe v7 of
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v11
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                  (coe
                                     du_mapAna'7496''45''8764'_164 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v1) (coe v8) (coe v13) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_call_118 v8 v9 v10
        -> case coe v7 of
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v15
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v19 ->
                              coe
                                du_anaBlock'7496'_156 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v10 v19) (coe v18 v19) (coe v15 v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_halt_122 v8 v9
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._._.mapAnaᵈ-∼
d_mapAna'7496''45''8764'_164 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7496''45''8764'_164 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                             v11
  = du_mapAna'7496''45''8764'_164 v0 v1 v5 v6 v7 v8 v9 v10 v11
du_mapAna'7496''45''8764'_164 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7496''45''8764'_164 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v8
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             du_ana'7496''45''8764'_144 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           du_mapAna'7496''45''8764'_164 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v9) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           du_mapAna'7496''45''8764'_164 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v10) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_mapAna'7496''45''8764'_164 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v9) (coe v11) (coe v13) (coe v15))
                                  (coe
                                     du_mapAna'7496''45''8764'_164 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v10) (coe v12) (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-relᵍ
d_in'45'rel'7501'_236 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_in'45'rel'7501'_236 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_in'45'rel'7501'_236 v2 v3 v4 v5 v6
du_in'45'rel'7501'_236 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_in'45'rel'7501'_236 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v6 -> erased
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_in'45'rel'7501'_236 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_in'45'rel'7501'_236 (coe v10) (coe v8) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_in'45'rel'7501'_236 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_in'45'rel'7501'_236 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-run
d_in'45'run_300 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_in'45'run_300 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_in'45'run_300 v2 v3 v5 v7 v8 v9 v10
du_in'45'run_300 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_in'45'run_300 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'691'_622
      (coe
         MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased)
      (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
            (coe v0) (coe v1))
         (coe v3))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'691'_622
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
            (coe v0) (coe v1))
         (coe v2) (coe v3) (coe v6)
         (coe
            (\ v7 v8 v9 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe v5 v7 v8 v9)))))
      (coe
         (\ v7 v8 v9 ->
            case coe v9 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                -> case coe v11 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                       -> coe
                            du_in'45'rel'7501'_236 (coe v0) (coe v1) (coe v4 v7) (coe v10)
                            (coe v13)
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.GradedAnaBridge.ana-bridgeᵍ
d_ana'45'bridge'7501'_350 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_ana'45'bridge'7501'_350 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> coe
                    du_ana'7510''45''8764'_64 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v3))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v3 erased
                            (coe
                               MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v3) (coe v4)
                               (coe v5 v13))))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v3 erased)
                            (coe
                               MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe v3) (coe v4))
                               (coe v6 v13))))
                    (coe du_cr_374 (coe v3) (coe v4) (coe v5) (coe v6) (coe v11))
                    (coe v8) (coe v9) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> coe
                    du_ana'7496''45''8764'_144 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v3))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                            (coe du_g_406 (coe v3) (coe v4)) (coe v5 v13)))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                            (coe
                               MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v3 erased)
                            (coe
                               MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                  (coe v3) (coe v4))
                               (coe v6 v13))))
                    (coe
                       d_cr_474 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v11) (coe v12) (coe v8) (coe v9) (coe v10))
                    (coe v8) (coe v9) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cr_374 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13
  = du_cr_374 v2 v3 v4 v5 v6 v11 v12 v13
du_cr_374 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_cr_374 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
         (coe
            (\ v8 ->
               coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
                 (coe
                    MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v0) (coe v1)
                    (coe v8))))
         (coe
            MAlonzo.Code.Once.Lang.Graded.du_toT'8734'_146
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
            (coe v2 v5))
         (coe
            MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
            (coe
               MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased)
            (coe
               MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                  (coe v0) (coe v1))
               (coe v3 v6)))
         (coe
            du_in'45'run_300 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Graded.du_toT'8734'_146
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
               (coe v2 v5))
            (coe v3 v6) (coe (\ v8 -> v8)) (coe (\ v8 v9 v10 -> v10))
            (coe v4 v5 v6 v7))
         (coe (\ v8 v9 v10 -> v10)))
-- Once.Adequacy.GradedAnaBridge._.g
d_g_406 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_g_406 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_g_406 v2 v3 v11
du_g_406 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_g_406 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
      (coe
         MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v0) (coe v1)
         (coe v2))
-- Once.Adequacy.GradedAnaBridge._.emb-map
d_emb'45'map_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_emb'45'map_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13 v14
  = du_emb'45'map_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_emb'45'map_420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_emb'45'map_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_embed_136
         (coe
            MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
            (coe du_g_406 (coe v2) (coe v3)) (coe v11)))
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
         (coe MAlonzo.Code.Once.Lang.Iterative.du_embed_136 (coe v11))
         (coe
            (\ v14 ->
               coe
                 MAlonzo.Code.Once.Lang.Iterative.du_embed_136
                 (coe
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114
                    (coe du_g_406 (coe v2) (coe v3) (coe v14))))))
      (coe v12)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
         (coe v11)
         (coe
            (\ v14 ->
               coe
                 MAlonzo.Code.Once.Lang.Trace.C_ret_114
                 (coe du_g_406 (coe v2) (coe v3) (coe v14)))))
      (coe
         du_emb'45'fmap_442 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v13)
         (coe MAlonzo.Code.Once.Lang.Iterative.du_embed_136 (coe v11))
         (coe v12) (coe v13))
-- Once.Adequacy.GradedAnaBridge._._.emb-fmap
d_emb'45'fmap_442 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_emb'45'fmap_442 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                  v14 ~v15 v16 v17 v18
  = du_emb'45'fmap_442
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v16 v17 v18
du_emb'45'fmap_442 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_emb'45'fmap_442 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_emb'45'fmapB_456 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v13)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v14))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v15))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v16)))
-- Once.Adequacy.GradedAnaBridge._._.emb-fmapB
d_emb'45'fmapB_456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_emb'45'fmapB_456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12 v13
                   v14 ~v15 v16 v17 v18
  = du_emb'45'fmapB_456
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14 v16 v17 v18
du_emb'45'fmapB_456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_emb'45'fmapB_456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16
  = case coe v16 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v19
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v19
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v19
        -> case coe v14 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v20
               -> case coe v20 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> case coe v15 of
                           MAlonzo.Code.Once.Lang.Trace.C_ret_114 v22
                             -> case coe v22 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_emb'45'fmap_442 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                            (coe v10) (coe v11) (coe v12) (coe v13) (coe v21)
                                            (coe v23) (coe v19))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v21
        -> case coe v14 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v22 v23 v24
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v25 v26 v27
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v28 ->
                              coe
                                du_emb'45'fmapB_456 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                                (coe v12) (coe v13) (coe v24 v28) (coe v27 v28) (coe v21 v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_474 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cr_474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_emb'45'map_420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v4 v11)
      (coe
         MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
         (coe
            MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased)
         (coe
            MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_358
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
               (coe v2) (coe v3))
            (coe v5 v12)))
      (coe
         du_in'45'run_300 (coe v2) (coe v3)
         (coe MAlonzo.Code.Once.Lang.Iterative.du_embed_136 (coe v4 v11))
         (coe v5 v12) (coe (\ v14 -> v14)) (coe (\ v14 v15 v16 -> v16))
         (coe v6 v11 v12 v13))
