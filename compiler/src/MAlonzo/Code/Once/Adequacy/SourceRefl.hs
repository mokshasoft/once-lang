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

module MAlonzo.Code.Once.Adequacy.SourceRefl where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.EnvRel
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.Sub
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Denotation.ValueRelPER
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Laws.SubLaws
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Adequacy.SourceRefl.cata-clo-rel
d_cata'45'clo'45'rel_24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_cata'45'clo'45'rel_24 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_cata'45'clo'45'rel_24 v1 v4 v5 v6 v7 v8
du_cata'45'clo'45'rel_24 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_cata'45'clo'45'rel_24 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_sem'45'cata'45'rel_1512
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
         (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v2)))
      (coe
         MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
         (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v3)))
      (coe
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                 (coe v6))
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_370 (coe v0)
                 (coe v7))
              (coe
                 (\ v9 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                      (coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v2))
                      (coe
                         (\ v10 ->
                            coe
                              v10
                              (coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                 (coe v0) (coe v1) (coe v9))))))
              (coe
                 (\ v9 ->
                    coe
                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                      (coe
                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v3))
                      (coe
                         (\ v10 ->
                            coe
                              v10
                              (coe
                                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                                 (coe v0) (coe v1) (coe v9))))))
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_seqF'8734''45'rel_1058
                 (coe v0) (coe v6) (coe v7) (coe v8))
              (coe
                 (\ v9 v10 v11 ->
                    coe
                      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                         (coe
                            v4
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                               (coe v0) (coe v1) (coe v9))
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                               (coe v0) (coe v1) (coe v10))
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'8315''185''45'rel_1188
                               (coe v0) (coe v1) (coe v9) (coe v10) (coe v11))))))))
      (coe v5)
-- Once.Adequacy.SourceRefl.ana-clo-rel
d_ana'45'clo'45'rel_64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_ana'45'clo'45'rel_64 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_ana'45'clo'45'rel_64 v1 v4 v5 v6 v7 v8 v9 v10
du_ana'45'clo'45'rel_64 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
du_ana'45'clo'45'rel_64 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_ana'7477''45'rel_1422
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
         (coe v0))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578 v0
                 erased)
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe v2 v8))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578 v0
                 erased)
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe v3 v8))))
      (coe
         (\ v8 v9 v10 ->
            coe
              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe v2 v8))
              (coe
                 MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe v3 v9))
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 (coe v0))
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 (coe v0))
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                 (coe v2 v8) (coe v3 v9)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                    (coe v0) (coe v1))
                 (coe v4 v8 v9 v10)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueRel.du_cfD'45'rel_1112 (coe v0)
                    (coe v1)))
              (coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_cμin'45'rel_1246
                 (coe v0))))
      (coe v5) (coe v6) (coe v7)
-- Once.Adequacy.SourceRefl.RelDefs
d_RelDefs_78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 -> ()
d_RelDefs_78 = erased
-- Once.Adequacy.SourceRefl.<:-rel
d_'60''58''45'rel_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''58''45'rel_98 ~v0 v1 v2 v3 v4 v5
  = du_'60''58''45'rel_98 v1 v2 v3 v4 v5
du_'60''58''45'rel_98 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''58''45'rel_98 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
        -> coe (\ v5 -> v5)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
        -> coe (\ v5 -> v5)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
        -> coe (\ v5 -> v5)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v12 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         (\ v23 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                              (coe v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                              (coe v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe v23)
                                              (coe
                                                 du_'60''58''45'rel_98 (coe v17) (coe v22)
                                                 (coe v13)))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         (\ v23 v24 v25 v26 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                              (coe
                                                 v3
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v24)))
                                              (coe
                                                 v4
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v25)))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe
                                                 v23
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v24))
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v25))
                                                 (coe
                                                    du_'60''58''45'rel_98 v20 v15 v12 v24 v25 v26))
                                              (coe
                                                 du_'60''58''45'rel_98 (coe v17) (coe v22)
                                                 (coe v13)))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         (\ v23 v24 v25 v26 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                              (coe
                                                 v3
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v24)))
                                              (coe
                                                 v4
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v25)))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                 (coe v17) (coe v22) (coe v13))
                                              (coe
                                                 v23
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v24))
                                                 (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                    (coe v20) (coe v15) (coe v12) (coe v25))
                                                 (coe
                                                    du_'60''58''45'rel_98 v20 v15 v12 v24 v25 v26))
                                              (coe
                                                 du_'60''58''45'rel_98 (coe v17) (coe v22)
                                                 (coe v13)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v13 v14
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                    -> coe
                                         (\ v19 ->
                                            case coe v19 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        du_'60''58''45'rel_98 v11 v13 v9 v15 v17
                                                        v20)
                                                     (coe
                                                        du_'60''58''45'rel_98 v12 v14 v10 v16 v18
                                                        v21)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v13 v14
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                                    -> coe
                                         (\ v17 -> coe du_'60''58''45'rel_98 v11 v13 v9 v15 v16 v17)
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                    -> coe (\ v17 -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                                    -> coe (\ v17 -> MAlonzo.RTE.mazUnreachableError)
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                    -> coe
                                         (\ v17 ->
                                            coe du_'60''58''45'rel_98 v12 v14 v10 v15 v16 v17)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62
        -> coe (\ v6 -> v6)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v8
        -> coe (\ v9 -> v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceRefl.<:-trans-rel
d_'60''58''45'trans'45'rel_174 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''58''45'trans'45'rel_174 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_'60''58''45'trans'45'rel_174 v1 v2 v3 v4 v5 v6 v7
du_'60''58''45'trans'45'rel_174 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''58''45'trans'45'rel_174 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
        -> coe
             (\ v7 ->
                coe
                  du_'60''58''45'rel_98
                  (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) v2 v4
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v7)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
        -> coe
             (\ v7 ->
                coe
                  du_'60''58''45'rel_98
                  (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) v2 v4 v5 v6 v7)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
        -> coe
             (\ v7 ->
                coe
                  du_'60''58''45'rel_98
                  (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) v2 v4 v5 v6 v7)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v14 v15 v16
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v22 v23 v24
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v25 v26
                                    -> case coe v20 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v34 v35 v36
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v37 v38 v39
                                                         -> case coe v38 of
                                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v40 v41
                                                                -> coe
                                                                     (\ v42 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             (coe v24) (coe v39)
                                                                             (coe v35))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v22)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v26))
                                                                                (coe v24))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                v14 v15 v16)
                                                                             v5
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v37)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v41))
                                                                                (coe v39))
                                                                             (MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                (coe v0)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v26))
                                                                                   (coe v24))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v37)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v41))
                                                                                   (coe v39))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v14 v15 v16)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v34 v35 v36))
                                                                             v6
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                                             (coe
                                                                                v5
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                             (coe
                                                                                v6
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v24)
                                                                                (coe v15))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v39)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                   (coe v19)
                                                                                   (coe v24)
                                                                                   (coe v39)
                                                                                   (coe v15)
                                                                                   (coe v35)))
                                                                             (coe v42)
                                                                             (coe
                                                                                du_'60''58''45'trans'45'rel_174
                                                                                (coe v19) (coe v24)
                                                                                (coe v39) (coe v15)
                                                                                (coe v35)))
                                                                          (coe
                                                                             (\ v43 v44 v45 ->
                                                                                v45)))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v34 v35 v36
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v37 v38 v39
                                                         -> case coe v38 of
                                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v40 v41
                                                                -> coe
                                                                     (\ v42 v43 v44 v45 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             (coe v24) (coe v39)
                                                                             (coe v35))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v22)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v26))
                                                                                (coe v24))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                v14 v15 v16)
                                                                             v5
                                                                             (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v37) (coe v22)
                                                                                (coe v34)
                                                                                (coe v43)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v37)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v41))
                                                                                (coe v39))
                                                                             (MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                (coe v0)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v26))
                                                                                   (coe v24))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v37)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v41))
                                                                                   (coe v39))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v14 v15 v16)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v34 v35 v36))
                                                                             v6 v44)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                                             (coe
                                                                                v5
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v22)
                                                                                   (coe v17)
                                                                                   (coe v14)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v34)
                                                                                      (coe v43))))
                                                                             (coe
                                                                                v6
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v37)
                                                                                   (coe v17)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v17)
                                                                                      (coe v34)
                                                                                      (coe v14))
                                                                                   (coe v44)))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v24)
                                                                                (coe v15))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v39)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                   (coe v19)
                                                                                   (coe v24)
                                                                                   (coe v39)
                                                                                   (coe v15)
                                                                                   (coe v35)))
                                                                             (coe
                                                                                v42
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v22)
                                                                                   (coe v17)
                                                                                   (coe v14)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v34)
                                                                                      (coe v43)))
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v37)
                                                                                   (coe v17)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v17)
                                                                                      (coe v34)
                                                                                      (coe v14))
                                                                                   (coe v44))
                                                                                (coe
                                                                                   du_'60''58''45'trans'45'rel_174
                                                                                   v37 v22 v17 v34
                                                                                   v14 v43 v44 v45))
                                                                             (coe
                                                                                du_'60''58''45'trans'45'rel_174
                                                                                (coe v19) (coe v24)
                                                                                (coe v39) (coe v15)
                                                                                (coe v35)))
                                                                          (coe
                                                                             (\ v46 v47 v48 ->
                                                                                v48)))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v34 v35 v36
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v37 v38 v39
                                                         -> case coe v38 of
                                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v40 v41
                                                                -> coe
                                                                     (\ v42 v43 v44 v45 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'737'_556
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             (coe v24) (coe v39)
                                                                             (coe v35))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v22)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v26))
                                                                                (coe v24))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                v14 v15 v16)
                                                                             v5
                                                                             (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v37) (coe v22)
                                                                                (coe v34)
                                                                                (coe v43)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                             v0
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v37)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe v20)
                                                                                   (coe v41))
                                                                                (coe v39))
                                                                             (MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                (coe v0)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v26))
                                                                                   (coe v24))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                   (coe v37)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                      (coe v20)
                                                                                      (coe v41))
                                                                                   (coe v39))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v14 v15 v16)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                                                   v34 v35 v36))
                                                                             v6 v44)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
                                                                             (coe
                                                                                v5
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v22)
                                                                                   (coe v17)
                                                                                   (coe v14)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v34)
                                                                                      (coe v43))))
                                                                             (coe
                                                                                v6
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v37)
                                                                                   (coe v17)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v17)
                                                                                      (coe v34)
                                                                                      (coe v14))
                                                                                   (coe v44)))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v24)
                                                                                (coe v15))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                (coe v19) (coe v39)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                   (coe v19)
                                                                                   (coe v24)
                                                                                   (coe v39)
                                                                                   (coe v15)
                                                                                   (coe v35)))
                                                                             (coe
                                                                                v42
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v22)
                                                                                   (coe v17)
                                                                                   (coe v14)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v34)
                                                                                      (coe v43)))
                                                                                (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                                   (coe v37)
                                                                                   (coe v17)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Internal.Laws.SubLaws.d_'60''58''45'trans_86
                                                                                      (coe v37)
                                                                                      (coe v22)
                                                                                      (coe v17)
                                                                                      (coe v34)
                                                                                      (coe v14))
                                                                                   (coe v44))
                                                                                (coe
                                                                                   du_'60''58''45'trans'45'rel_174
                                                                                   v37 v22 v17 v34
                                                                                   v14 v43 v44 v45))
                                                                             (coe
                                                                                du_'60''58''45'trans'45'rel_174
                                                                                (coe v19) (coe v24)
                                                                                (coe v39) (coe v15)
                                                                                (coe v35)))
                                                                          (coe
                                                                             (\ v46 v47 v48 ->
                                                                                v48)))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v15 v16
                      -> case coe v4 of
                           MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v21 v22
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Internal.Type.C__'42'__24 v23 v24
                                    -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                           -> case coe v6 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                  -> coe
                                                       (\ v29 ->
                                                          case coe v29 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      du_'60''58''45'trans'45'rel_174
                                                                      v13 v15 v23 v11 v21 v25 v27
                                                                      v30)
                                                                   (coe
                                                                      du_'60''58''45'trans'45'rel_174
                                                                      v14 v16 v24 v12 v22 v26 v28
                                                                      v31)
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v15 v16
                      -> case coe v4 of
                           MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v21 v22
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Internal.Type.C__'43'__26 v23 v24
                                    -> case coe v5 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                                           -> case coe v6 of
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                                                  -> coe
                                                       (\ v27 ->
                                                          coe
                                                            du_'60''58''45'trans'45'rel_174 v13 v15
                                                            v23 v11 v21 v25 v26 v27)
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                                                  -> coe (\ v27 -> MAlonzo.RTE.mazUnreachableError)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                                           -> case coe v6 of
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                                                  -> coe (\ v27 -> MAlonzo.RTE.mazUnreachableError)
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                                                  -> coe
                                                       (\ v27 ->
                                                          coe
                                                            du_'60''58''45'trans'45'rel_174 v14 v16
                                                            v24 v12 v22 v25 v26 v27)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62
        -> coe (\ v8 -> coe du_'60''58''45'rel_98 v0 v2 v4 v5 v6 v8)
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v10
        -> coe seq (coe v4) (coe (\ v11 -> v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceRefl.<:-refl-relʳ
d_'60''58''45'refl'45'rel'691'_292 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''58''45'refl'45'rel'691'_292 ~v0 v1 v2 v3 v4
  = du_'60''58''45'refl'45'rel'691'_292 v1 v2 v3 v4
du_'60''58''45'refl'45'rel'691'_292 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''58''45'refl'45'rel'691'_292 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'sym_512 v0
      (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v0) (coe v0)
         (coe
            MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84 (coe v0))
         (coe v2))
      v1
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'60''58''45'refl'45'rel_72 v0 v2
         v1
         (coe
            MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'sym_512 v0 v1 v2
            v3))
-- Once.Adequacy.SourceRefl._.sigOp-rel
d_sigOp'45'rel_318 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_sigOp'45'rel_318 v0 ~v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9
  = du_sigOp'45'rel_318 v0 v2 v4 v5 v6 v7
du_sigOp'45'rel_318 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_sigOp'45'rel_318 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'embed_764
      (coe
         MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
               (coe
                  MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1)))
            (coe v2) (coe v3) (coe v4)
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
               (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
               (coe v5)))
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Once.Internal.Trace.C_ret_114
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                    (coe v6)))))
      (coe
         MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
               (coe
                  MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1)))
            (coe v2) (coe v3) (coe v4)
            (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
               (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
               (coe v5)))
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Once.Internal.Trace.C_ret_114
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                    (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                    (coe v6)))))
      (coe
         MAlonzo.Code.Once.Denotation.EvalRel.du_RelT'8242''45'refl_284
         (coe
            MAlonzo.Code.Once.Denotation.ValueRel.d_base'45'refl_420 (coe v3)
            (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4)))
         (coe
            MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpSemT_32 (coe v0)
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
                  (coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1)))
               (coe v2) (coe v3) (coe v4)
               (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
                  (coe v2) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
                  (coe v5)))
            (coe
               (\ v6 ->
                  coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
                       (coe v3) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4))
                       (coe v6))))))
-- Once.Adequacy.SourceRefl._.SD-rel
d_SD'45'rel_352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_SD'45'rel_352 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 v9 v10 v11
  = du_SD'45'rel_352 v0 v1 v2 v3 v4 v5 v7 v8 v9 v10 v11
du_SD'45'rel_352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_SD'45'rel_352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe
                MAlonzo.Code.Once.Adequacy.EnvRel.du_lookup'45'rel_94 (coe v5)
                (coe v13) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v14 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                      -> case coe v24 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  seq (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                     (coe
                                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                                        (coe addInt (coe (1 :: Integer)) (coe v4))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5)
                                           (coe v21))
                                        (coe v23) (coe v20) (coe v8) (coe v9) (coe v10)))
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 du_SD'45'rel_352 (coe v0) (coe v1) (coe v2)
                                                 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'44'__16
                                                    (coe v5) (coe v21))
                                                 (coe v23) (coe v20) (coe v8) (coe v9) (coe v10)))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 du_SD'45'rel_352 (coe v0) (coe v1) (coe v2)
                                                 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'44'__16
                                                    (coe v5) (coe v21))
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v14 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 du_SD'45'rel_352 (coe v0) (coe v1) (coe v2)
                                                 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'44'__16
                                                    (coe v5) (coe v21))
                                                 (coe v23) (coe v20) (coe v8) (coe v9) (coe v10)))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 du_SD'45'rel_352 (coe v0) (coe v1) (coe v2)
                                                 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'44'__16
                                                    (coe v5) (coe v21))
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (coe
                                            (\ v26 v27 v28 ->
                                               coe
                                                 du_SD'45'rel_352 (coe v0) (coe v1) (coe v2)
                                                 (coe v3) (coe addInt (coe (1 :: Integer)) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'44'__16
                                                    (coe v5) (coe v21))
                                                 (coe v23) (coe v20)
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v8) (coe v26))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                    (coe v14) (coe v9) (coe v27))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10) (coe v28))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v13 v14 v15 v17 v18 v19
        -> case coe v17 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       (\ v20 -> coe v20 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                    (coe
                       (\ v20 -> coe v20 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v10)))
                    (coe (\ v20 v21 v22 -> v22))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                          (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14)))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14))))
                             (coe v8))))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                          (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14)))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14))))
                             (coe v9))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v10)))
                    (coe
                       (\ v20 v21 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v8)))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v9)))
                            (coe v20) (coe v21)
                            (coe
                               du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe v5) (coe v15) (coe v19)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v10)))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                          (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14)))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14))))
                             (coe v8))))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                          (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14)))
                             (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14)))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                   (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                      (coe v17) (coe v14))))
                             (coe v9))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v17)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v18)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v17)
                                (coe v14)))
                          (coe v10)))
                    (coe
                       (\ v20 v21 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v8)))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v15) (coe v19) (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v9)))
                            (coe v20) (coe v21)
                            (coe
                               du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe v5) (coe v15) (coe v19)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v17) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14)))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                        (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe v17) (coe v14))))
                                  (coe v10)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v13 v14 v15 v18 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                           (coe
                              (\ v26 v27 v28 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v23))
                                      (coe v19) (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v8)))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v23))
                                      (coe v19) (coe v0) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v9)))
                                   (coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe
                                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                         (coe v4) (coe v5) (coe v15) (coe v20) (coe v0) (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                               (coe v14)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v14)))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v14))))
                                            (coe v8))))
                                   (coe
                                      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                      (coe
                                         MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                         (coe v4) (coe v5) (coe v15) (coe v20) (coe v0) (coe v2)
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                               (coe v14)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v14)))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                  (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v14))))
                                            (coe v9))))
                                   (coe
                                      du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v23))
                                      (coe v19)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v8))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v9))
                                      (coe
                                         MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v10)))
                                   (coe
                                      (\ v29 v30 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                           (coe
                                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                              (coe v4) (coe v5) (coe v15) (coe v20) (coe v0)
                                              (coe v1)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14)))
                                                 (coe v14)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14)))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))))
                                                 (coe v8)))
                                           (coe
                                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                              (coe v4) (coe v5) (coe v15) (coe v20) (coe v0)
                                              (coe v2)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14)))
                                                 (coe v14)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14)))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))))
                                                 (coe v9)))
                                           (coe v29) (coe v30)
                                           (coe
                                              du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                                              (coe v4) (coe v5) (coe v15) (coe v20)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14)))
                                                 (coe v14)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14)))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))))
                                                 (coe v8))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14)))
                                                 (coe v14)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14)))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))))
                                                 (coe v9))
                                              (coe
                                                 MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14)))
                                                 (coe v14)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14)))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                                       (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                       (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))))
                                                 (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v13 v14 v17 v18
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v19 v20
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v19) (coe v17) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v19) (coe v17) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v9)))
                    (coe
                       (\ v21 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v20) (coe v18) (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v8)))
                            (coe
                               (\ v22 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v22))))))
                    (coe
                       (\ v21 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v20) (coe v18) (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v9)))
                            (coe
                               (\ v22 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v22))))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v19) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                             (coe v14))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                             (coe v13) (coe v14))
                          (coe v10)))
                    (coe
                       (\ v21 v22 v23 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v20) (coe v18) (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v8)))
                            (coe
                               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                               (coe v4) (coe v5) (coe v20) (coe v18) (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v9)))
                            (coe
                               (\ v24 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                       (coe v24))))
                            (coe
                               (\ v24 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v22)
                                       (coe v24))))
                            (coe
                               du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe v5) (coe v20) (coe v18)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v8))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v9))
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                     (coe v14))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                     (coe v13) (coe v14))
                                  (coe v10)))
                            (coe
                               (\ v24 v25 v26 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v23)
                                       (coe v26))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16) (coe v0) (coe v2) (coe v9))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v17))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v17))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v6) (coe v15))
                (coe v16) (coe v8) (coe v9) (coe v10))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v19))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v14 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16) (coe v0) (coe v2) (coe v9))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v17))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v17))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v14) (coe v6))
                (coe v16) (coe v8) (coe v9) (coe v10))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v19))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v17) (coe v16) (coe v0) (coe v1) (coe v8))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v17) (coe v16) (coe v0) (coe v2) (coe v9))
                    (coe
                       (\ v19 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v19))))
                    (coe
                       (\ v19 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v19))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v17) (coe v16) (coe v8) (coe v9) (coe v10))
                    (coe
                       (\ v19 v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v18) (coe v16) (coe v0) (coe v1) (coe v8))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v18) (coe v16) (coe v0) (coe v2) (coe v9))
                    (coe
                       (\ v19 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v19))))
                    (coe
                       (\ v19 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v19))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v18) (coe v16) (coe v8) (coe v9) (coe v10))
                    (coe
                       (\ v19 v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v13 v14 v15 v16 v17 v18 v19 v21 v22 v23
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v18) (coe v19))
                (coe v21) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v18) (coe v19))
                (coe v21) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v9)))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v24 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v4))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v18))
                     (coe v6) (coe v22) (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                              (coe v15))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                              (coe v14) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe v8)))
                        (coe v24)))
                (\ v24 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v4))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v19))
                     (coe v6) (coe v23) (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v17)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                              (coe v15))
                           (coe v15)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                              (coe v14) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe v8)))
                        (coe v24))))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v24 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v4))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v18))
                     (coe v6) (coe v22) (coe v0) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                              (coe v15))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                              (coe v14) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe v9)))
                        (coe v24)))
                (\ v24 ->
                   coe
                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v4))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v19))
                     (coe v6) (coe v23) (coe v0) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v17)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                              (coe v15))
                           (coe v15)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                              (coe v14) (coe v15))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                                 (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100
                                    (coe v14) (coe v15)))
                              (coe v9)))
                        (coe v24))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v18) (coe v19))
                (coe v21)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v14)
                         (coe v15)))
                   (coe v10)))
             (coe
                du_'46'extendedlambda0_552 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v13) (coe v14) (coe v15) (coe v16)
                (coe v17) (coe v18) (coe v19) (coe v22) (coe v23) (coe v8) (coe v9)
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v15
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Void_22)
                (coe v15) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Void_22)
                (coe v15) (coe v0) (coe v2) (coe v9))
             (\ v16 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             (\ v16 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Void_22) (coe v15)
                (coe v8) (coe v9) (coe v10))
             (coe
                (\ v16 v17 v18 ->
                   coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v13 v14 v15 v16 v18 v19
        -> case coe v15 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                    (coe v6) (coe v19)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v8))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v9))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v14)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                          (coe v14)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                             (coe v13)))
                       (coe v10))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v16) (coe v18) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v16) (coe v18) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v9)))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19) (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v8))
                               (coe v20))))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19) (coe v0) (coe v2)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v9))
                               (coe v20))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v16) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'One_292
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v10)))
                    (coe
                       (\ v20 v21 v22 ->
                          coe
                            du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v8))
                               (coe v20))
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v9))
                               (coe v21))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v10))
                               (coe v22))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v16) (coe v18) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5) (coe v16) (coe v18) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v9)))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19) (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v8))
                               (coe v20))))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19) (coe v0) (coe v2)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v9))
                               (coe v20))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v16) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13)))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                             (coe v13)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                (coe v13))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v15)
                                   (coe v13))))
                          (coe v10)))
                    (coe
                       (\ v20 v21 v22 ->
                          coe
                            du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v16))
                            (coe v6) (coe v19)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v8))
                               (coe v20))
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v9))
                               (coe v21))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                     (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                        (coe v15) (coe v13)))
                                  (coe v10))
                               (coe v22))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             erased
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             erased
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v14) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v14) (coe v0) (coe v2) (coe v9))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v0) (coe v2)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v14)
                (coe v8) (coe v9) (coe v10))
             (\ v15 v16 v17 ->
                coe
                  du_sigOp'45'rel_318 (coe v0) (coe v2)
                  (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                  (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                  (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136) v15)
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v14) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v14) (coe v0) (coe v2) (coe v9))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v0) (coe v2)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v14)
                (coe v8) (coe v9) (coe v10))
             (\ v15 v16 v17 ->
                coe
                  du_sigOp'45'rel_318 (coe v0) (coe v2)
                  (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                  (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                  (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124) v15)
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe v15) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9)))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                (\ v17 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v18 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v18))))))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v15)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                      (coe v14))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                      (coe v13) (coe v14))
                   (coe v10)))
             (coe
                (\ v17 v18 v19 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v1)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8)))
                     (coe
                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                        (coe v4) (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                        (coe v16) (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9)))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v1)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17) (coe v20))))
                     (coe
                        (\ v20 ->
                           MAlonzo.Code.Once.Denotation.SourceDenote.d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) (coe v20))))
                     (coe
                        du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                        (coe v5) (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v16)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v8))
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v9))
                        (coe
                           MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                              (coe v14))
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                              (coe v13) (coe v14))
                           (coe v10)))
                     (coe
                        (\ v20 v21 v22 ->
                           coe
                             du_sigOp'45'rel_318 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                (coe v20))))))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap_528
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe v14) (coe v17) (coe v0) (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe v14) (coe v17) (coe v0) (coe v2) (coe v9))
             (coe
                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                (coe v14) (coe v6) (coe v16))
             (coe
                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                (coe v14) (coe v6) (coe v16))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v14) (coe v17) (coe v8) (coe v9) (coe v10))
             (coe du_'60''58''45'rel_98 (coe v14) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v14 v15
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2) (coe v6) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v21
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                           -> case coe v15 of
                                                MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v25 v26
                                                  -> coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                       (coe
                                                          du_sigOp'45'rel_318 (coe v0) (coe v2)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                          (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                             (coe v14)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                                                             (coe v26))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                _ -> erased
                                         MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                           -> case coe v15 of
                                                MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v25 v26
                                                  -> coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                       (coe
                                                          du_sigOp'45'rel_318 (coe v0) (coe v2)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                          (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                             (coe v18) (coe v17) (coe v14)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                                                             (coe v26))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                _ -> erased
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> case coe v15 of
                                         MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v24 v25
                                           -> coe
                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                (coe
                                                   du_sigOp'45'rel_318 (coe v0) (coe v2)
                                                   (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                   (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                      (coe v18) (coe v17) (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                                                      (coe v25))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                         _ -> erased
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (\ v26 v27 v28 ->
                                            coe
                                              du_sigOp'45'rel_318 (coe v0) (coe v2) (coe v16)
                                              (coe v18)
                                              (coe
                                                 MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                 (coe v18) (coe v17) (coe v14) (coe v24) (coe v25))
                                              v26)
                                  _ -> erased
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                         (\ v26 v27 v28 ->
                                            coe
                                              du_sigOp'45'rel_318 (coe v0) (coe v2) (coe v16)
                                              (coe v18)
                                              (coe
                                                 MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                 (coe v18) (coe v17) (coe v14) (coe v24) (coe v25))
                                              v26)
                                  _ -> erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v17
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v17))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'base_38 v19
                      -> coe
                           du_sigOp'45'rel_318 (coe v0) (coe v2)
                           (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                              (coe v14)
                              (coe MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10)
                              (coe v19))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v14
        -> coe
             MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
             (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1))
             (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v6)
             (coe
                MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v6)
                (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v14)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v13
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v3 v13 v6
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v14
        -> coe
             du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Internal.Context.C_'8709'_8) (coe v6)
             (coe v14) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                    (coe
                       MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
                       (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1))
                       (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)) (coe v17)
                       (coe v19) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v13 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe v14) (coe v17) (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))))
                   (coe v8)))
             (coe
                MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                (coe v4) (coe v5) (coe v14) (coe v17) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))))
                   (coe v9)))
             (coe
                (\ v18 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                     (coe v0)
                     (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)) (coe v16)
                     (coe v18)))
             (coe
                (\ v18 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                     (coe v0)
                     (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v2))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6)) (coe v16)
                     (coe v18)))
             (coe
                du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v14) (coe v17)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))))
                   (coe v8))
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))))
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                   (coe v13)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                      (coe v13)
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                         (coe v13))
                      (coe
                         MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56 (coe v4))
                         (coe
                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))))
                   (coe v10)))
             (coe
                MAlonzo.Code.Once.Denotation.EvalRel.d_liftFn'45'rel_1302 (coe v0)
                (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v1))
                (coe MAlonzo.Code.Once.Denotation.SourceDenote.d_calls_80 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)) (coe v14)
                (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v13 v14 v16 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                           (coe
                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                              (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                 (coe v23))
                              (coe v19) (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v8)))
                           (coe
                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                              (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                 (coe v23))
                              (coe v19) (coe v0) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v9)))
                           (coe
                              (\ v26 ->
                                 coe
                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v8)))
                                   (coe
                                      (\ v27 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v28 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                   (coe v27 v28) (coe v26)))))))
                           (coe
                              (\ v26 ->
                                 coe
                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v9)))
                                   (coe
                                      (\ v27 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v28 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                   (coe v27 v28) (coe v26)))))))
                           (coe
                              du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                 (coe v23))
                              (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                    (coe v13)
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                                 (coe v10)))
                           (coe
                              (\ v26 v27 v28 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v8)))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                      (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v16))
                                      (coe v20) (coe v0) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v9)))
                                   (coe
                                      (\ v29 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v30 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                   (coe v29 v30) (coe v26)))))
                                   (coe
                                      (\ v29 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              (\ v30 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                   (coe v29 v30) (coe v27)))))
                                   (coe
                                      du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                         (coe v21)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                         (coe v16))
                                      (coe v20)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v8))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v9))
                                      (coe
                                         MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe v13)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14)))
                                         (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45'trans_278
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                               (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v14))))
                                         (coe v10)))
                                   (coe
                                      (\ v29 v30 v31 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                           (coe
                                              (\ v32 v33 v34 ->
                                                 coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                   (coe v29 v32) (coe v30 v33) (coe v26) (coe v27)
                                                   (coe v31 v32 v33 v34) (coe v28)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v13 v14 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v21 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v24 v25
                      -> case coe v22 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v23))
                                     (coe v19) (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v8)))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v23))
                                     (coe v19) (coe v0) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9)))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v28 v29)))))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v28 v29)))))
                                  (coe
                                     du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v24)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v23))
                                     (coe v19)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v8))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9))
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v10)))
                                  (coe
                                     (\ v28 v29 v30 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20) (coe v0) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v28 v31)))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v29 v31)))
                                          (coe
                                             du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v25)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v27))
                                                (coe v23))
                                             (coe v20)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9))
                                             (coe
                                                MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v10)))
                                          (coe
                                             (\ v31 v32 v33 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe
                                                     (\ v34 v35 v36 ->
                                                        case coe v34 of
                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v37
                                                            -> case coe v35 of
                                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v38
                                                                   -> coe v30 v37 v38 v36
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v37
                                                            -> case coe v35 of
                                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v38
                                                                   -> coe v33 v37 v38 v36
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v13 v14 v19 v20
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v21 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v24 v25
                      -> case coe v23 of
                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                        (coe v26))
                                     (coe v19) (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v8)))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                        (coe v26))
                                     (coe v19) (coe v0) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9)))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v30 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                          (coe v28 v30)
                                                          (coe
                                                             (\ v31 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v29 v30)
                                                                  (coe
                                                                     (\ v32 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v31)
                                                                             (coe v32))))))))))))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v30 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                          (coe v28 v30)
                                                          (coe
                                                             (\ v31 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v29 v30)
                                                                  (coe
                                                                     (\ v32 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v31)
                                                                             (coe v32))))))))))))
                                  (coe
                                     du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v25))
                                        (coe v26))
                                     (coe v19)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v8))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v9))
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v13) (coe v14))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''737'_224
                                           (coe v13) (coe v14))
                                        (coe v10)))
                                  (coe
                                     (\ v28 v29 v30 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20) (coe v0) (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9)))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v32 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                          (coe v28 v32)
                                                          (coe
                                                             (\ v33 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v31 v32)
                                                                  (coe
                                                                     (\ v34 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v33)
                                                                             (coe v34))))))))))
                                          (coe
                                             (\ v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v32 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                          (coe v29 v32)
                                                          (coe
                                                             (\ v33 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v31 v32)
                                                                  (coe
                                                                     (\ v34 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v33)
                                                                             (coe v34))))))))))
                                          (coe
                                             du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v25))
                                                (coe v27))
                                             (coe v20)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v9))
                                             (coe
                                                MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                   (coe v13) (coe v14))
                                                (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v13) (coe v14))
                                                (coe v10)))
                                          (coe
                                             (\ v31 v32 v33 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe
                                                     (\ v34 v35 v36 ->
                                                        coe
                                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                          (coe v28 v34) (coe v29 v35)
                                                          (coe
                                                             (\ v37 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v31 v34)
                                                                  (coe
                                                                     (\ v38 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v37)
                                                                             (coe v38))))))
                                                          (coe
                                                             (\ v37 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                  (coe v32 v35)
                                                                  (coe
                                                                     (\ v38 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v37)
                                                                             (coe v38))))))
                                                          (coe v30 v34 v35 v36)
                                                          (coe
                                                             (\ v37 v38 v39 ->
                                                                coe
                                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                                  (coe v31 v34) (coe v32 v35)
                                                                  (coe
                                                                     (\ v40 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v37) (coe v40))))
                                                                  (coe
                                                                     (\ v40 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v38) (coe v40))))
                                                                  (coe v33 v34 v35 v36)
                                                                  (coe
                                                                     (\ v40 v41 v42 ->
                                                                        coe
                                                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v39)
                                                                             (coe v42))))))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v19
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v22 of
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v23 v24 v25
                      -> case coe v24 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v26 v27
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v20)
                                           (coe v23))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v25))
                                     (coe v19) (coe v0) (coe v1) (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v20)
                                           (coe v23))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v25))
                                     (coe v19) (coe v0) (coe v2) (coe v9))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v30 ->
                                                        coe
                                                          v28
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v29) (coe v30))))))))
                                  (coe
                                     (\ v28 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                          (coe
                                             (\ v29 ->
                                                coe
                                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                  (coe
                                                     (\ v30 ->
                                                        coe
                                                          v28
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v29) (coe v30))))))))
                                  (coe
                                     du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v20)
                                           (coe v23))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v27))
                                        (coe v25))
                                     (coe v19) (coe v8) (coe v9) (coe v10))
                                  (coe
                                     (\ v28 v29 v30 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                          (coe
                                             (\ v31 v32 v33 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                  (coe
                                                     (\ v34 v35 v36 ->
                                                        coe
                                                          v30
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v31) (coe v34))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v32) (coe v35))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v33) (coe v36))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v13 v17 v18
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v19 v20 v21
               -> case coe v19 of
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v22
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                           (coe v22) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v21))
                                     (coe v18) (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                           (coe v13))
                                        (coe v8)))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                                     (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                           (coe v22) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v21))
                                     (coe v18) (coe v0) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                           (coe v13))
                                        (coe v9)))
                                  (coe
                                     (\ v25 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                          (coe
                                             MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538
                                             (coe v22) (coe v17)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                                                (coe v22) (coe v17)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                   (coe v25))))))
                                  (coe
                                     (\ v25 ->
                                        coe
                                          MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                          (coe
                                             MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538
                                             (coe v22) (coe v17)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.SourceDenote.du_cata'45'ev'45'alg'738'_36
                                                (coe v22) (coe v17)
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                   (coe v25))))))
                                  (coe
                                     du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                           (coe v22) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v21))
                                     (coe v18)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                           (coe v13))
                                        (coe v8))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                           (coe v13))
                                        (coe v9))
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                           (coe v13))
                                        (coe v10)))
                                  (coe
                                     (\ v25 v26 v27 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                          (\ v28 v29 v30 ->
                                             coe
                                               du_cata'45'clo'45'rel_24 (coe v22) (coe v17)
                                               (coe v25) (coe v26) (coe v27) v28)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v13 v18 v19
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v22 of
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                           (coe
                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                              (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v20)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v24)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v23)
                                    (coe v20)))
                              (coe v19) (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                    (coe v13))
                                 (coe v8)))
                           (coe
                              MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                              (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v20)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v24)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v23)
                                    (coe v20)))
                              (coe v19) (coe v0) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                    (coe v13))
                                 (coe v9)))
                           (coe
                              (\ v25 ->
                                 coe
                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                   (coe
                                      (\ v26 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              MAlonzo.Code.Once.Internal.StreamInf.du_anaF'7477'_150
                                              v23
                                              (\ v27 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                                                   (coe
                                                      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                      (coe v23) (coe v18))
                                                   (coe v25 v27))
                                              v26)))))
                           (coe
                              (\ v25 ->
                                 coe
                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                   (coe
                                      (\ v26 ->
                                         coe
                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                           (coe
                                              MAlonzo.Code.Once.Internal.StreamInf.du_anaF'7477'_150
                                              v23
                                              (\ v27 ->
                                                 coe
                                                   MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                                                   (coe
                                                      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                      (coe v23) (coe v18))
                                                   (coe v25 v27))
                                              v26)))))
                           (coe
                              du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v20)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v24)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v23)
                                    (coe v20)))
                              (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                    (coe v13))
                                 (coe v8))
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                    (coe v13))
                                 (coe v9))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                                    (coe v13))
                                 (coe v10)))
                           (coe
                              (\ v25 v26 v27 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                   (coe
                                      (\ v28 v29 v30 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                           (coe
                                              du_ana'45'clo'45'rel_64 (coe v23) (coe v18) (coe v25)
                                              (coe v26) (coe v27) (coe v28) (coe v29) (coe v30))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v13 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v17)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v19) (coe v17)))
                       (coe v16) (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v13))
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_122
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v17)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v19) (coe v17)))
                       (coe v16) (coe v0) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v13))
                          (coe v9)))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               MAlonzo.Code.Once.Internal.Iterative.du_iter'8734'_256 (coe v20))))
                    (coe
                       (\ v20 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               MAlonzo.Code.Once.Internal.Iterative.du_iter'8734'_256 (coe v20))))
                    (coe
                       du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v17)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v19) (coe v17)))
                       (coe v16)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v13))
                          (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v13))
                          (coe v9))
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                          (coe v13)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''42'Many_304
                             (coe v13))
                          (coe v10)))
                    (coe
                       (\ v20 v21 v22 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                            (coe
                               (\ v23 v24 v25 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'iter'8734'_622
                                    (coe v20) (coe v21) (coe (\ v26 v27 v28 -> v28)) (coe v22)
                                    (coe v23) (coe v24) (coe v25)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceRefl._..extendedlambda0
d_'46'extendedlambda0_552 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'46'extendedlambda0_552 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 ~v14 v15 v16 v17 v18 v19 v20 v21 v22
  = du_'46'extendedlambda0_552
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17 v18 v19
      v20 v21 v22
du_'46'extendedlambda0_552 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Once.Denotation.SourceDenote.T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'46'extendedlambda0_552 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
  = case coe v19 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
        -> case coe v20 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v23
               -> coe
                    du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v12))
                    (coe v6) (coe v14)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v16)))
                       (coe v22))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v17)))
                       (coe v23))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''737'_330
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v18)))
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
        -> case coe v20 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
               -> coe
                    du_SD'45'rel_352 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4))
                    (coe
                       MAlonzo.Code.Once.Internal.Context.du__'44'__16 (coe v5) (coe v13))
                    (coe v6) (coe v15)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v16)))
                       (coe v22))
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v17)))
                       (coe v23))
                    (coe
                       MAlonzo.Code.Once.Adequacy.EnvRel.du_bind'45'rel_132 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                             (coe v9))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''8852''691'_346
                             (coe v8) (coe v9))
                          (coe
                             MAlonzo.Code.Once.Adequacy.EnvRel.du_restrict'45'rel_20 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'8849''7512''45''43''691'_240
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                                   (coe v9)))
                             (coe v18)))
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
