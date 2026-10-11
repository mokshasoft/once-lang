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
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.GradedOps
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.GradedCataBridge._.RelGM
d_RelGM_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGM_10 = erased
-- Once.Adequacy.GradedCataBridge._.RelGV
d_RelGV_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_14 = erased
-- Once.Adequacy.GradedCataBridge.out-relR
d_out'45'relR_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'relR_32 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_out'45'relR_32 v1 v2 v6 v7 v8
du_out'45'relR_32 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'relR_32 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v6 -> erased
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v9 v10
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
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v9 v10
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
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_z'45'rel'7501'_100 ~v0 v1 v2 ~v3 v4 v5 v6
  = du_z'45'rel'7501'_100 v1 v2 v4 v5 v6
du_z'45'rel'7501'_100 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_z'45'rel'7501'_100 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v7
               -> coe
                    MAlonzo.Code.Once.Adequacy.GradedRelation.du_injB'45'rel_390
                    (coe v7) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v4
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v9 v10
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
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v9 v10
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
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
d_seqF'45'rel'7510'_152 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_seqF'45'rel'7510'_152 v1 v5 v6 v7
du_seqF'45'rel'7510'_152 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
du_seqF'45'rel'7510'_152 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_12 v4
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_616 v3
      MAlonzo.Code.Once.Spec.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_418
                           (coe MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 (coe v6))
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                              (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel'7510'_152 (coe v4) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_418
                           (coe MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 (coe v6))
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v5)
                              (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel'7510'_152 (coe v5) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_368
                                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                                     (coe v8))
                                  (coe
                                     du_seqF'45'rel'7510'_152 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_368
                                          (coe
                                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                             v7)
                                          (coe
                                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                             (coe v5) (coe v9))
                                          (coe
                                             du_seqF'45'rel'7510'_152 (coe v5) (coe v7) (coe v9)
                                             (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_616
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.alg-step
d_alg'45'step_264 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
d_alg'45'step_264 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_alg'45'step_264 v1 v2 v4 v7 v8 v9 v10
du_alg'45'step_264 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
du_alg'45'step_264 v0 v1 v2 v3 v4 v5 v6
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_368
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v4)))
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v5)))
             (coe
                du_seqF'45'rel'7510'_152 (coe v1)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v4))
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v5))
                (coe
                   du_out'45'relR_32 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)))
             (coe
                (\ v7 v8 v9 ->
                   coe
                     v3
                     (coe
                        MAlonzo.Code.Once.Denotation.GradedOps.du_cf'8315''185''7515'_132
                        (coe v1) (coe v2) (coe v7))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_440
                        (coe v1) (coe v2) (coe v8))
                     (coe
                        du_z'45'rel'7501'_100 (coe v1) (coe v2) (coe v7) (coe v8)
                        (coe v9))))
      MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_368
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v4)))
             (coe
                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v5)))
             (coe
                MAlonzo.Code.Once.Adequacy.SeqRel.du_seqF'45'rel_88 (coe v1)
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v4))
                (coe
                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                   (coe v1) (coe v2) (coe v5))
                (coe
                   du_out'45'relR_32 (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)))
             (coe
                (\ v7 v8 v9 ->
                   coe
                     v3
                     (coe
                        MAlonzo.Code.Once.Denotation.GradedOps.du_cf'8315''185''7515'_132
                        (coe v1) (coe v2) (coe v7))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_440
                        (coe v1) (coe v2) (coe v8))
                     (coe
                        du_z'45'rel'7501'_100 (coe v1) (coe v2) (coe v7) (coe v8)
                        (coe v9))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedCataBridge.cata-bridgeᵍ
d_cata'45'bridge'7501'_346 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
d_cata'45'bridge'7501'_346 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_cata'45'bridge'7501'_346 v1 v2 v4 v5 v6 v7 v8
du_cata'45'bridge'7501'_346 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_604
du_cata'45'bridge'7501'_346 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v1))
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Once.Denotation.GradedDomain.du_bindM_28 (coe v0)
              (coe
                 MAlonzo.Code.Once.Denotation.GradedOps.du_seqM_176 (coe v0)
                 (coe v1)
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe v1) (coe v2) (coe v7)))
              (coe
                 (\ v8 ->
                    coe
                      v3
                      (coe
                         MAlonzo.Code.Once.Denotation.GradedOps.du_cf'8315''185''7515'_132
                         (coe v1) (coe v2) (coe v8))))))
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v1)
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe v1) (coe v2) (coe v7)))
              (coe
                 (\ v8 ->
                    coe
                      v4
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_440
                         (coe v1) (coe v2) (coe v8))))))
      (coe du_alg'45'step_264 (coe v0) (coe v1) (coe v2) (coe v5))
      (coe v6)
