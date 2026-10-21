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
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Graded
import qualified MAlonzo.Code.Once.Internal.GradedOps
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Stream
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedCataBridge._.RelGM
d_RelGM_10 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()
d_RelGM_10 = erased
-- Once.Adequacy.GradedCataBridge._.RelGV
d_RelGV_16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> ()
d_RelGV_16 = erased
-- Once.Adequacy.GradedCataBridge.out-relR
d_out'45'relR_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'relR_34 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_out'45'relR_34 v1 v2 v6 v7 v8
du_out'45'relR_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'relR_34 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_out'45'relR_34 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_out'45'relR_34 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_out'45'relR_34 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_out'45'relR_34 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.z-relᵍ
d_z'45'rel'7501'_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_z'45'rel'7501'_102 ~v0 v1 v2 ~v3 v4 v5 v6
  = du_z'45'rel'7501'_102 v1 v2 v4 v5 v6
du_z'45'rel'7501'_102 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_z'45'rel'7501'_102 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'K_52 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v7
               -> coe
                    MAlonzo.Code.Once.Adequacy.GradedRelation.du_injB'45'rel_532
                    (coe v7) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_z'45'rel'7501'_102 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_z'45'rel'7501'_102 (coe v10) (coe v8) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_z'45'rel'7501'_102 (coe v9) (coe v7) (coe v11)
                                            (coe v13) (coe v15))
                                         (coe
                                            du_z'45'rel'7501'_102 (coe v10) (coe v8) (coe v12)
                                            (coe v14) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.seqF-relᵖ
d_seqF'45'rel'7510'_154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_seqF'45'rel'7510'_154 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'45'rel'7510'_154 v1 v5 v6 v7
du_seqF'45'rel'7510'_154 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_seqF'45'rel'7510'_154 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe v3)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v6))
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                 (coe v7))
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                              (coe du_seqF'45'rel'7510'_154 (coe v4) (coe v6) (coe v7) (coe v3))
                              (coe (\ v8 v9 v10 -> v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v6))
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                                 (coe v7))
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                              (coe du_seqF'45'rel'7510'_154 (coe v5) (coe v6) (coe v7) (coe v3))
                              (coe (\ v8 v9 v10 -> v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe v4) (coe v8))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                (coe v7))
                                             (coe
                                                (\ v13 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12) (coe v13))))))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                (coe v5) (coe v9))
                                             (coe
                                                (\ v13 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12) (coe v13))))))
                                     (coe
                                        du_seqF'45'rel'7510'_154 (coe v4) (coe v6) (coe v8)
                                        (coe v10))
                                     (coe
                                        (\ v12 v13 v14 ->
                                           coe
                                             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                (coe v7))
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                (coe v5) (coe v9))
                                             (coe
                                                (\ v15 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12) (coe v15))))
                                             (coe
                                                (\ v15 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v13) (coe v15))))
                                             (coe
                                                du_seqF'45'rel'7510'_154 (coe v5) (coe v7) (coe v9)
                                                (coe v11))
                                             (coe
                                                (\ v15 v16 v17 ->
                                                   coe
                                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v14) (coe v17)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.emb-ret
d_emb'45'ret_238 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_emb'45'ret_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_emb'45'ret_238 v6
du_emb'45'ret_238 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_emb'45'ret_238 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v0)
-- Once.Adequacy.GradedCataBridge.seqF-relᵃ
d_seqF'45'rel'7491'_258 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_seqF'45'rel'7491'_258 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'45'rel'7491'_258 v1 v5 v6 v7
du_seqF'45'rel'7491'_258 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_seqF'45'rel'7491'_258 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4
        -> coe du_emb'45'ret_238 (coe v3)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                              (coe
                                 MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v0) (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                 (coe
                                    MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4) (coe v6)))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                      (coe
                                         MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                         (coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8))))))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                              (coe v2))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                              (coe
                                 MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4) (coe v6))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8)))))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                 (coe
                                    MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4) (coe v6)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                 (coe v7))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                      (coe
                                         MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8)))))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8))))
                              (coe du_seqF'45'rel'7491'_258 (coe v4) (coe v6) (coe v7) (coe v3))
                              (coe (\ v8 v9 -> coe du_emb'45'ret_238)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                              (coe
                                 MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v0) (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                 (coe
                                    MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v5) (coe v6)))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                      (coe
                                         MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                         (coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))))))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                              (coe v2))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                              (coe
                                 MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v5) (coe v6))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8)))))
                           (coe
                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                 (coe
                                    MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v5) (coe v6)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                                 (coe v7))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                      (coe
                                         MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8)))))
                              (coe
                                 (\ v8 ->
                                    coe
                                      MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v8))))
                              (coe du_seqF'45'rel'7491'_258 (coe v5) (coe v6) (coe v7) (coe v3))
                              (coe (\ v8 v9 -> coe du_emb'45'ret_238)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                     (coe
                                        MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v0)
                                        (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                        (coe
                                           MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4)
                                           (coe v6)))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                             (coe
                                                MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                   (coe v5) (coe v7))
                                                (coe
                                                   (\ v13 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) (coe v13))))))))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                                     (coe v2))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                                     (coe
                                        MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4)
                                        (coe v6))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
                                             (coe
                                                MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                (coe v5) (coe v7))
                                             (coe
                                                (\ v13 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12) (coe v13)))))))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                        (coe
                                           MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v4)
                                           (coe v6)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                        (coe v4) (coe v8))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                             (coe
                                                MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                   (coe v5) (coe v7))
                                                (coe
                                                   (\ v13 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) (coe v13)))))))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                (coe v5) (coe v9))
                                             (coe
                                                (\ v13 ->
                                                   coe
                                                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12) (coe v13))))))
                                     (coe
                                        du_seqF'45'rel'7491'_258 (coe v4) (coe v6) (coe v8)
                                        (coe v10))
                                     (coe
                                        (\ v12 v13 v14 ->
                                           coe
                                             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
                                                   (coe
                                                      MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                      (coe v5) (coe v7))
                                                   (coe
                                                      (\ v15 ->
                                                         coe
                                                           MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v12) (coe v15))))))
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                                   (coe
                                                      MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                      (coe v5) (coe v7)))
                                                (coe
                                                   (\ v15 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v12) (coe v15))))))
                                             (coe
                                                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                   (coe v5) (coe v9))
                                                (coe
                                                   (\ v15 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v13) (coe v15)))))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                   (coe v5) (coe v7))
                                                (coe
                                                   (\ v15 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) (coe v15)))))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                                   (coe
                                                      MAlonzo.Code.Once.Internal.Stream.du_seqF_34
                                                      (coe v5) (coe v7)))
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                                   (coe v5) (coe v9))
                                                (coe
                                                   (\ v15 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Trace.C_ret_114
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v12) (coe v15)))))
                                                (coe
                                                   (\ v15 ->
                                                      coe
                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v13) (coe v15))))
                                                (coe
                                                   du_seqF'45'rel'7491'_258 (coe v5) (coe v7)
                                                   (coe v9) (coe v11))
                                                (coe
                                                   (\ v15 v16 v17 ->
                                                      coe
                                                        du_emb'45'ret_238
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v14) (coe v17))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.seqF∞-rel
d_seqF'8734''45'rel_356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_seqF'8734''45'rel_356 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'8734''45'rel_356 v1 v5 v6 v7
du_seqF'8734''45'rel_356 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_seqF'8734''45'rel_356 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v4
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe v3)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                              (coe v6))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                              (coe v7))
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                           (coe du_seqF'8734''45'rel_356 (coe v4) (coe v6) (coe v7) (coe v3))
                           (coe (\ v8 v9 v10 -> v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                              (coe v6))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v5)
                              (coe v7))
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                           (coe du_seqF'8734''45'rel_356 (coe v5) (coe v6) (coe v7) (coe v3))
                           (coe (\ v8 v9 v10 -> v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v4)
                                     (coe v8))
                                  (coe
                                     (\ v12 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v7))
                                          (coe
                                             (\ v13 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v13))))))
                                  (coe
                                     (\ v12 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v9))
                                          (coe
                                             (\ v13 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v13))))))
                                  (coe
                                     du_seqF'8734''45'rel_356 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v7))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370
                                             (coe v5) (coe v9))
                                          (coe
                                             (\ v15 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) (coe v15))))
                                          (coe
                                             (\ v15 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v13) (coe v15))))
                                          (coe
                                             du_seqF'8734''45'rel_356 (coe v5) (coe v7) (coe v9)
                                             (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.alg-step
d_alg'45'step_454 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_alg'45'step_454 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
  = du_alg'45'step_454 v2 v3 v5 v6 v7 v8 v9 v10 v11
du_alg'45'step_454 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_alg'45'step_454 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v6)))
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v7)))
                (coe
                   (\ v9 ->
                      coe
                        MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42
                           (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                        (coe
                           v3
                           (coe
                              MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                              (coe v1) (coe v2) (coe v9)))))
                (coe
                   (\ v9 ->
                      coe
                        v4
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                           (coe v1) (coe v2) (coe v9))))
                (coe
                   du_seqF'45'rel'7510'_154 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v6))
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v7))
                   (coe
                      du_out'45'relR_34 (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)))
                (coe
                   (\ v9 v10 v11 ->
                      coe
                        v5
                        (coe
                           MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                           (coe v1) (coe v2) (coe v9))
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                           (coe v1) (coe v2) (coe v10))
                        (coe
                           du_z'45'rel'7501'_102 (coe v1) (coe v2) (coe v9) (coe v10)
                           (coe v11)))))
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
             (coe
                MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                (coe
                   MAlonzo.Code.Once.Internal.Graded.du_bindM_80
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                      (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                   (coe
                      MAlonzo.Code.Once.Internal.GradedOps.du_seqM_244 (coe v0) (coe v1)
                      (coe
                         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                         (coe v2) (coe v6)))
                   (coe
                      (\ v9 ->
                         coe
                           v3
                           (coe
                              MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                              (coe v1) (coe v2) (coe v9))))))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                   (coe
                      MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                         (coe v2) (coe v6))))
                (coe
                   (\ v9 ->
                      coe
                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                        (coe
                           v3
                           (coe
                              MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                              (coe v1) (coe v2) (coe v9))))))
             (coe
                MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
                (coe v1) (coe v2) (coe v4)
                (coe
                   MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v7)))
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                (coe
                   MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v6)))
                (coe
                   (\ v9 ->
                      coe
                        v3
                        (coe
                           MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                           (coe v1) (coe v2) (coe v9)))))
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                   (coe
                      MAlonzo.Code.Once.Internal.Stream.du_seqF_34 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                         (coe v2) (coe v6))))
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v7)))
                (coe
                   (\ v9 ->
                      coe
                        MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                        (coe
                           v3
                           (coe
                              MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                              (coe v1) (coe v2) (coe v9)))))
                (coe
                   (\ v9 ->
                      coe
                        v4
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                           (coe v1) (coe v2) (coe v9))))
                (coe
                   du_seqF'45'rel'7491'_258 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v6))
                   (coe
                      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                      (coe v2) (coe v7))
                   (coe
                      du_out'45'relR_34 (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)))
                (coe
                   (\ v9 v10 v11 ->
                      coe
                        v5
                        (coe
                           MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                           (coe v1) (coe v2) (coe v9))
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                           (coe v1) (coe v2) (coe v10))
                        (coe
                           du_z'45'rel'7501'_102 (coe v1) (coe v2) (coe v9) (coe v10)
                           (coe v11)))))
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Internal.GradedOps.du_seqM_244 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6)))
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v1)
                (coe
                   MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v7)))
             (coe
                (\ v9 ->
                   coe
                     v3
                     (coe
                        MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v9))))
             (coe
                (\ v9 ->
                   coe
                     v4
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                        (coe v1) (coe v2) (coe v9))))
             (coe
                du_seqF'8734''45'rel_356 (coe v1)
                (coe
                   MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v6))
                (coe
                   MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v1)
                   (coe v2) (coe v7))
                (coe
                   du_out'45'relR_34 (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)))
             (coe
                (\ v9 v10 v11 ->
                   coe
                     v5
                     (coe
                        MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                        (coe v1) (coe v2) (coe v9))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                        (coe v1) (coe v2) (coe v10))
                     (coe
                        du_z'45'rel'7501'_102 (coe v1) (coe v2) (coe v9) (coe v10)
                        (coe v11))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.cata-bridgeᵍ
d_cata'45'bridge'7501'_544 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'bridge'7501'_544 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 ~v10
                           ~v11
  = du_cata'45'bridge'7501'_544 v1 v2 v3 v5 v6 v7 v8 v9
du_cata'45'bridge'7501'_544 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_cata'45'bridge'7501'_544 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
         (coe v2))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Internal.Graded.du_bindM_80 (coe v0)
              (coe
                 MAlonzo.Code.Once.Internal.GradedOps.du_seqM_244 (coe v1) (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v2)
                    (coe v3) (coe v8)))
              (coe
                 (\ v9 ->
                    coe
                      v4
                      (coe
                         MAlonzo.Code.Once.Internal.GradedOps.du_cf'8315''185''7515'_200
                         (coe v2) (coe v3) (coe v9))))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v2)
                 (coe
                    MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 (coe v2)
                    (coe v3) (coe v8)))
              (coe
                 (\ v9 ->
                    coe
                      v5
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                         (coe v2) (coe v3) (coe v9))))))
      (coe
         du_alg'45'step_454 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
      (coe v7)
