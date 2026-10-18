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
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueDomainLaws
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.GradedOps
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_
d__'8764''7510''7496'__10 a0 a1 a2 a3 = ()
-- Once.Adequacy.GradedAnaBridge._._∼∞ᵈ_
d__'8764''8734''7496'__14 a0 a1 a2 a3 = ()
-- Once.Adequacy.GradedAnaBridge._.RelGT
d_RelGT_20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGT_20 = erased
-- Once.Adequacy.GradedAnaBridge._.RelGV
d_RelGV_24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_24 = erased
-- Once.Adequacy.GradedAnaBridge._._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_30 ::
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_force'45''8764''7510''7496'_30 v0
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_force'45''8764''7510''7496'_24
      (coe v0)
-- Once.Adequacy.GradedAnaBridge._._∼∞ᵈ_.force-∼∞ᵈ
d_force'45''8764''8734''7496'_34 ::
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''8734''7496'__34 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_force'45''8764''8734''7496'_34 v0
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.d_force'45''8764''8734''7496'_44
      (coe v0)
-- Once.Adequacy.GradedAnaBridge.anaᵖ-∼
d_ana'7510''45''8764'_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
d_ana'7510''45''8764'_54 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_ana'7510''45''8764'_54 v0 v1 v5 v6 v7 v8 v9 v10
du_ana'7510''45''8764'_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''7510''7496'__14
du_ana'7510''45''8764'_54 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.C_constructor_26
      (coe
         du_anaTree'7510'_74 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v2 v5) (coe v3 v6) (coe v4 v5 v6 v7))
-- Once.Adequacy.GradedAnaBridge.anaTreeᵖ
d_anaTree'7510'_74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_anaTree'7510'_74 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_anaTree'7510'_74 v0 v1 v5 v6 v7 v8 v9 v10
du_anaTree'7510'_74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_anaTree'7510'_74 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v11
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                    (coe
                       du_mapAna'7510''45''8764'_96 (coe v0) (coe v1) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.mapAnaᵖ-∼
d_mapAna'7510''45''8764'_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7510''45''8764'_96 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
                            v11
  = du_mapAna'7510''45''8764'_96 v0 v1 v2 v6 v7 v8 v9 v10 v11
du_mapAna'7510''45''8764'_96 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7510''45''8764'_96 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v8
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             du_ana'7510''45''8764'_54 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           du_mapAna'7510''45''8764'_96 (coe v0) (coe v1) (coe v9) (coe v3)
                           (coe v4) (coe v5) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           du_mapAna'7510''45''8764'_96 (coe v0) (coe v1) (coe v10) (coe v3)
                           (coe v4) (coe v5) (coe v11) (coe v12) (coe v8)
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
                                     du_mapAna'7510''45''8764'_96 (coe v0) (coe v1) (coe v9)
                                     (coe v3) (coe v4) (coe v5) (coe v11) (coe v13) (coe v15))
                                  (coe
                                     du_mapAna'7510''45''8764'_96 (coe v0) (coe v1) (coe v10)
                                     (coe v3) (coe v4) (coe v5) (coe v12) (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.ana∞-∼
d_ana'8734''45''8764'_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''8734''7496'__34
d_ana'8734''45''8764'_198 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_ana'8734''45''8764'_198 v0 v1 v5 v6 v7 v8 v9 v10
du_ana'8734''45''8764'_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.GradedRelation.T__'8764''8734''7496'__34
du_ana'8734''45''8764'_198 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.C_constructor_46
      (coe
         du_tree'8734''45''8764'_204 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v3 v6) (coe v4 v5 v6 v7))
-- Once.Adequacy.GradedAnaBridge._.tree∞-∼
d_tree'8734''45''8764'_204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_tree'8734''45''8764'_204 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 ~v8 v9 v10
  = du_tree'8734''45''8764'_204 v0 v1 v5 v6 v7 v9 v10
du_tree'8734''45''8764'_204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
du_tree'8734''45''8764'_204 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518 v8 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                    (coe
                       MAlonzo.Code.Once.Lang.Iterative.du_mapAna'8734'_338 (coe v1)
                       (coe v1) (coe v2) (coe v8))
                    (coe
                       du_mapAna'8734''45''8764'_212 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v1) (coe v8) (coe v12) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532 v10 v13
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.Lang.Iterative.du_anaTree'8734'_324 (coe v1)
                         (coe v2) (coe v10 v17))
                    (\ v17 ->
                       coe
                         du_tree'8734''45''8764'_204 (coe v0) (coe v1) (coe v2) (coe v3)
                         (coe v4) (coe v16 v17) (coe v13 v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.mapAna∞-∼
d_mapAna'8734''45''8764'_212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'8734''45''8764'_212 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                             v11
  = du_mapAna'8734''45''8764'_212 v0 v1 v5 v6 v7 v8 v9 v10 v11
du_mapAna'8734''45''8764'_212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'8734''45''8764'_212 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v8
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             du_ana'8734''45''8764'_198 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           du_mapAna'8734''45''8764'_212 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v9) (coe v11) (coe v12) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe
                           du_mapAna'8734''45''8764'_212 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                     du_mapAna'8734''45''8764'_212 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v9) (coe v11) (coe v13) (coe v15))
                                  (coe
                                     du_mapAna'8734''45''8764'_212 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v10) (coe v12) (coe v14) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-relᵍ
d_in'45'rel'7501'_272 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_in'45'rel'7501'_272 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_in'45'rel'7501'_272 v2 v3 v4 v5 v6
du_in'45'rel'7501'_272 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_in'45'rel'7501'_272 v0 v1 v2 v3 v4
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
                                  du_in'45'rel'7501'_272 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_in'45'rel'7501'_272 (coe v10) (coe v8) (coe v11) (coe v12)
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
                                            du_in'45'rel'7501'_272 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_in'45'rel'7501'_272 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge.in-relᵍ-T
d_in'45'rel'7501''45'T_328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_in'45'rel'7501''45'T_328 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 v8
  = du_in'45'rel'7501''45'T_328 v2 v3 v6 v7 v8
du_in'45'rel'7501''45'T_328 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_in'45'rel'7501''45'T_328 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
      (coe v2) (coe v3)
      (coe
         (\ v5 v6 v7 ->
            coe
              du_in'45'rel'7501'_272 (coe v0) (coe v1) (coe v5) (coe v6)
              (coe v7)))
      (coe v4)
-- Once.Adequacy.GradedAnaBridge.anaSD
d_anaSD_360 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14
d_anaSD_360 ~v0 ~v1 v2 v3 ~v4 v5 = du_anaSD_360 v2 v3 v5
du_anaSD_360 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14
du_anaSD_360 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Stream.du_anaF'7496'_168 (coe v0)
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                 (coe v0) (coe v1))
              (coe
                 MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v2)
                 (coe (\ v4 -> coe v4 v3)))))
-- Once.Adequacy.GradedAnaBridge.ana-bridgeᵍ
d_ana'45'bridge'7501'_392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_ana'45'bridge'7501'_392 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_ana'45'bridge'7501'_392 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10
du_ana'45'bridge'7501'_392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_ana'45'bridge'7501'_392 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             du_ana'7510''45''8764'_54 (coe v0) (coe du_H_416 (coe v2))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased
                     (coe
                        MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v2) (coe v3)
                        (coe v4 v10))))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased)
                     (coe
                        MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                           (coe v2) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v5)
                           (coe (\ v11 -> coe v11 v10))))))
             (coe du_cr_424 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
             (coe v7) (coe v8) (coe v9)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Once.Denotation.ValueDomainLaws.du_ana'7496''45''8764'_152
             (coe du_H_468 (coe v2))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                     (coe
                        (\ v11 ->
                           coe
                             MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased
                             (coe
                                MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v2) (coe v3)
                                (coe v11))))
                     (coe v4 v10)))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                     (coe
                        MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2 erased)
                     (coe
                        MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                           (coe v2) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v5)
                           (coe (\ v11 -> coe v11 v10))))))
             (coe du_cr_478 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
             (coe v7) (coe v8) (coe v9)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v10
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v13
                      -> coe
                           du_ana'8734''45''8764'_198 (coe v0) (coe du_H_522 (coe v2))
                           (coe
                              (\ v14 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du_fmap'8734'_432
                                   (coe
                                      (\ v15 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2
                                           erased
                                           (coe
                                              MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158
                                              (coe v2) (coe v3) (coe v15))))
                                   (coe v4 v14)))
                           (coe
                              (\ v14 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                   (coe
                                      MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v2
                                      erased)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                      (coe
                                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                         (coe v2) (coe v3))
                                      (coe v10 v14))))
                           (coe du_cr_530 (coe v2) (coe v3) (coe v10) (coe v13)) (coe v7)
                           (coe v8) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedAnaBridge._.H
d_H_416 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_H_416 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_H_416 v2
du_H_416 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_H_416 v0
  = coe
      MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0)
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_424 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_cr_424 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_cr_424 v2 v3 v4 v5 v6 v10 v11 v12
du_cr_424 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_cr_424 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_in'45'rel'7501''45'T_328 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v2 v5))
      (coe
         MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v3)
         (coe (\ v8 -> coe v8 v6)))
      (coe
         du_kr_436 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.GradedAnaBridge._._.kr
d_kr_436 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_kr_436 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_kr_436 v4 v5 v6 v10 v11 v12
du_kr_436 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_kr_436 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'bind_218
      (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v0) (coe v1)
      (coe v2) (coe (\ v6 v7 v8 -> coe v8 v3 v4 v5))
-- Once.Adequacy.GradedAnaBridge._.H
d_H_468 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_H_468 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_H_468 v2
du_H_468 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_H_468 v0
  = coe
      MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0)
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_cr_478 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_cr_478 v2 v3 v4 v5 v6 v10 v11 v12
du_cr_478 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_cr_478 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_in'45'rel'7501''45'T_328 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
         (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v2)
         (coe (\ v8 -> coe v8 v5)))
      (coe
         MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v3)
         (coe (\ v8 -> coe v8 v6)))
      (coe
         du_kr_490 (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.GradedAnaBridge._._.kr
d_kr_490 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_kr_490 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_kr_490 v4 v5 v6 v10 v11 v12
du_kr_490 ::
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_kr_490 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'bind_218
      (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v0) (coe v1)
      (coe v2) (coe (\ v6 v7 v8 -> coe v8 v3 v4 v5))
-- Once.Adequacy.GradedAnaBridge._.H
d_H_522 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
d_H_522 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_H_522 v2
du_H_522 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6
du_H_522 v0
  = coe
      MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0)
-- Once.Adequacy.GradedAnaBridge._.cr
d_cr_530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_cr_530 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_cr_530 v2 v3 v5 v6 v10 v11 v12
du_cr_530 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
du_cr_530 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
      (coe v2 v5)
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
                 (coe
                    MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v0) (coe v1)
                    (coe v7)))))
      (coe v3 v4 v5 v6)
      (coe
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased
                 (coe
                    MAlonzo.Code.Once.Lang.GradedOps.du_cf'7515'_158 (coe v0) (coe v1)
                    (coe v7)))
              (coe
                 du_in'45'rel'7501'_272 (coe v0) (coe v1) (coe v7) (coe v8)
                 (coe v9))))
