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

module MAlonzo.Code.Once.Adequacy.GradedCataBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Adequacy.SeqRel
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.GradedOps
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedCataBridge._.RelGM
d_RelGM_10 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGM_10 = erased
-- Once.Adequacy.GradedCataBridge._.RelGV
d_RelGV_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_14 = erased
-- Once.Adequacy.GradedCataBridge.out-relR
d_out'45'relR_32 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'relR_32 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_out'45'relR_32 v1 v2 v6 v7 v8
du_out'45'relR_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'relR_32 v0 v1 v2 v3 v4
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
                                  du_out'45'relR_32 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_out'45'relR_32 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
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
                                            du_out'45'relR_32 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_out'45'relR_32 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.z-relᵍ
d_z'45'rel'7501'_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_z'45'rel'7501'_100 ~v0 v1 v2 ~v3 v4 v5 v6
  = du_z'45'rel'7501'_100 v1 v2 v4 v5 v6
du_z'45'rel'7501'_100 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_z'45'rel'7501'_100 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'K_52 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v7
               -> coe
                    MAlonzo.Code.Once.Adequacy.GradedRelation.du_injB'45'rel_504
                    (coe v7) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_z'45'rel'7501'_100 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_z'45'rel'7501'_100 (coe v10) (coe v8) (coe v11) (coe v12)
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
                                            du_z'45'rel'7501'_100 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_z'45'rel'7501'_100 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.seqF-relᵖ
d_seqF'45'rel'7510'_152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_seqF'45'rel'7510'_152 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'45'rel'7510'_152 v1 v5 v6 v7
du_seqF'45'rel'7510'_152 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_seqF'45'rel'7510'_152 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v4
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v3
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
                           (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v6))
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel'7510'_152 (coe v4) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
                           (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v6))
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5) (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel'7510'_152 (coe v5) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
                                  (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v6))
                                  (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v8))
                                  (coe
                                     du_seqF'45'rel'7510'_152 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
                                          (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v7)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5)
                                             (coe v9))
                                          (coe
                                             du_seqF'45'rel'7510'_152 (coe v5) (coe v7) (coe v9)
                                             (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.seqF∞-rel
d_seqF'8734''45'rel_254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_seqF'8734''45'rel_254 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'8734''45'rel_254 v1 v5 v6 v7
du_seqF'8734''45'rel_254 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
du_seqF'8734''45'rel_254 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v4
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
             v1 v3
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v7))
                           (coe
                              (\ v8 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8))))
                           (coe du_seqF'8734''45'rel_254 (coe v4) (coe v6) (coe v7) (coe v3))
                           (coe
                              (\ v8 v9 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5) (coe v7))
                           (coe
                              (\ v8 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))))
                           (coe du_seqF'8734''45'rel_254 (coe v5) (coe v6) (coe v7) (coe v3))
                           (coe
                              (\ v8 v9 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                                  (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v8))
                                  (coe
                                     (\ v12 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                                          (coe
                                             MAlonzo.Code.Once.Lang.Iterative.du_seqF'8734'_444
                                             (coe v5) (coe v7))
                                          (coe
                                             (\ v13 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v13))))))
                                  (coe
                                     du_seqF'8734''45'rel_254 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                                          (coe
                                             MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5)
                                             (coe v9))
                                          (coe
                                             (\ v15 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v15))))
                                          (coe
                                             du_seqF'8734''45'rel_254 (coe v5) (coe v7) (coe v9)
                                             (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v15))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.alg-step
d_alg'45'step_352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_alg'45'step_352 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 v8 v9 v10 v11
  = du_alg'45'step_352 v2 v3 v5 v6 v8 v9 v10 v11
du_alg'45'step_352 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_alg'45'step_352 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
             (coe
                MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v5)))
             (coe
                MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6)))
             (coe
                du_seqF'45'rel'7510'_152 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6))
                (coe
                   du_out'45'relR_32 (coe v1) (coe v2) (coe v5) (coe v6) (coe v7)))
             (coe
                (\ v8 v9 v10 ->
                   coe
                     v4
                     (coe
                        MAlonzo.Code.Once.Lang.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v8))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                        (coe v1) (coe v2) (coe v9))
                     (coe
                        du_z'45'rel'7501'_100 (coe v1) (coe v2) (coe v8) (coe v9)
                        (coe v10))))
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe
                MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6)))
             (coe
                (\ v8 ->
                   coe
                     v3
                     (coe
                        MAlonzo.Code.Once.Lang.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v8))))
             (coe
                du_seqF'8734''45'rel_254 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6))
                (coe
                   du_out'45'relR_32 (coe v1) (coe v2) (coe v5) (coe v6) (coe v7)))
             (coe
                (\ v8 v9 v10 ->
                   coe
                     v4
                     (coe
                        MAlonzo.Code.Once.Lang.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v8))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                        (coe v1) (coe v2) (coe v9))
                     (coe
                        du_z'45'rel'7501'_100 (coe v1) (coe v2) (coe v8) (coe v9)
                        (coe v10))))
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
             (coe
                MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v5)))
             (coe
                MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6)))
             (coe
                MAlonzo.Code.Once.Adequacy.SeqRel.du_seqF'45'rel_88 (coe v1)
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v5))
                (coe
                   MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6))
                (coe
                   du_out'45'relR_32 (coe v1) (coe v2) (coe v5) (coe v6) (coe v7)))
             (coe
                (\ v8 v9 v10 ->
                   coe
                     v4
                     (coe
                        MAlonzo.Code.Once.Lang.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v8))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                        (coe v1) (coe v2) (coe v9))
                     (coe
                        du_z'45'rel'7501'_100 (coe v1) (coe v2) (coe v8) (coe v9)
                        (coe v10))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.cata-bridgeᵍ
d_cata'45'bridge'7501'_456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_cata'45'bridge'7501'_456 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 ~v10
                           ~v11
  = du_cata'45'bridge'7501'_456 v1 v2 v3 v5 v6 v7 v8 v9
du_cata'45'bridge'7501'_456 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
du_cata'45'bridge'7501'_456 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v2))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Lang.Graded.du_bindM_80 (coe v0)
              (coe
                 MAlonzo.Code.Once.Lang.GradedOps.du_seqM_244 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v2)
                    (coe v3) (coe v8)))
              (coe
                 (\ v9 ->
                    coe
                      v4
                      (coe
                         MAlonzo.Code.Once.Lang.GradedOps.du_cf'8315''185''7515'_200
                         (coe v2) (coe v3) (coe v9))))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
              (coe
                 MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v2)
                 (coe
                    MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 (coe v2)
                    (coe v3) (coe v8)))
              (coe
                 (\ v9 ->
                    coe
                      v5
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                         (coe v2) (coe v3) (coe v9))))))
      (coe
         du_alg'45'step_352 (coe v1) (coe v2) (coe v3) (coe v4) (coe v6))
      (coe v7)
