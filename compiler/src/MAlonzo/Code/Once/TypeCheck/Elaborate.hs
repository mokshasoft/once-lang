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

module MAlonzo.Code.Once.TypeCheck.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Seq
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.isRIntVliftTarget?
d_isRIntVliftTarget'63'_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRIntVliftTarget'63'_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           erased))
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.isRFloatVliftTarget?
d_isRFloatVliftTarget'63'_24 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRFloatVliftTarget'63'_24 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           erased))
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.RPairTarget
d_RPairTarget_30 a0 = ()
data T_RPairTarget_30
  = C_rpt'45'prod_36 | C_rpt'45'vlift_46 | C_rpt'45'other_50
-- Once.TypeCheck.Elaborate.classifyRPairTarget
d_classifyRPairTarget_54 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_RPairTarget_30
d_classifyRPairTarget_54 v0
  = let v1 = coe C_rpt'45'other_50 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'42'__122 v2 v3 -> coe C_rpt'45'prod_36
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C__'42'__122 v7 v8 -> coe C_rpt'45'vlift_46
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_74 a0 a1 = ()
data T_InferElabResult_74
  = C_success_88 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_90 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_98 a0 a1 a2 = ()
data T_CheckElabResult_98
  = C_success_112 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_114 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.NegOperandView
d_NegOperandView_116 a0 = ()
data T_NegOperandView_116
  = C_nov'45'int_120 | C_nov'45'float_130 | C_nov'45'other_134
-- Once.TypeCheck.Elaborate.negOperandView
d_negOperandView_138 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NegOperandView_116
d_negOperandView_138 v0
  = let v1 = coe C_nov'45'other_134 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
           -> coe C_nov'45'int_120
         MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
           -> coe C_nov'45'float_130
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.soundOf
d_soundOf_156 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74 -> ()
d_soundOf_156 = erased
-- Once.TypeCheck.Elaborate.VerifiedInferResult
d_VerifiedInferResult_180 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_VerifiedInferResult_180 = erased
-- Once.TypeCheck.Elaborate.checkSoundOf
d_checkSoundOf_194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98 -> ()
d_checkSoundOf_194 = erased
-- Once.TypeCheck.Elaborate.VerifiedCheckResult
d_VerifiedCheckResult_222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_VerifiedCheckResult_222 = erased
-- Once.TypeCheck.Elaborate.GivenElabResult
d_GivenElabResult_240 a0 a1 a2 a3 = ()
data T_GivenElabResult_240
  = C_success_258 MAlonzo.Code.Once.Type.T_Type_108
                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_260 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.givenSoundOf
d_givenSoundOf_270 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> T_GivenElabResult_240 -> ()
d_givenSoundOf_270 = erased
-- Once.TypeCheck.Elaborate.VerifiedGivenResult
d_VerifiedGivenResult_306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> ()
d_VerifiedGivenResult_306 = erased
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_338 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer'45'dec_338 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = du_given'45'infer'45'dec_338
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_given'45'infer'45'dec_338 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer'45'dec_338 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
        -> if coe v12
             then case coe v13 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                      -> case coe v11 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                             -> if coe v15
                                  then case coe v16 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_success_258 (coe v2) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                         (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v4))
                                                         (coe v2))
                                                      (coe
                                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                                         v14
                                                         (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_164
                                                            (coe v2))
                                                         v17)
                                                      v6)
                                                   (coe v7) (coe v8))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860
                                                   v1 v4 v9 v14 v17)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v16)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_260
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                     (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe v3))
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe v4))
                                                     (coe v2))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v13)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_260
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
                                (coe v2))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-infer
d_given'45'infer_418 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer_418 ~v0 ~v1 v2 v3 v4
  = du_given'45'infer_418 v2 v3 v4
du_given'45'infer_418 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'infer_418 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> let v10
                        = coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_failure_260
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_Many_10
                                       -> coe
                                            du_given'45'infer'45'dec_338 (coe v0) (coe v11)
                                            (coe v13) (coe v1) (coe v15) (coe v6) (coe v7) (coe v8)
                                            (coe v9) (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
                                               (coe v0) (coe v11))
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__18
                                               (coe v15) (coe v1))
                                     _ -> coe v10
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v10)
             C_failure_90 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_260 (coe v5))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-dec
d_given'45'cata'45'dec_492 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'dec_492 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 v10
                           v11
  = du_given'45'cata'45'dec_492 v0 v4 v6 v8 v9 v10 v11
du_given'45'cata'45'dec_492 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'dec_492 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_success_258 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_512 v1 v3)
                          (coe addInt (coe (1 :: Integer)) (coe v4))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v1 v5))
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_260
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                             (coe ("cata" :: Data.Text.Text))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata_548 v0 ~v1 v2 v3 v4 v5
  = du_given'45'cata_548 v0 v2 v3 v4 v5
du_given'45'cata_548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata_548 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             C_success_88 v7 v8 v9 v10 v11
               -> let v12
                        = coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_failure_260
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                  (coe ("cata" :: Data.Text.Text))))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                         -> case coe v8 of
                              MAlonzo.Code.Once.Surface.Context.C_'91''93'_62
                                -> coe
                                     du_given'45'cata'45'dec_492 (coe v0) (coe v3) (coe v15)
                                     (coe v9) (coe v10) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1)
                                              (coe v15))
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                                           (coe v15)))
                              _ -> coe v12
                       _ -> coe v12)
             C_failure_90 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_260 (coe v7))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-void
d_given'45'cata'45'void_602 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'void_602 v0 ~v1 ~v2 v3
  = du_given'45'cata'45'void_602 v0 v3
du_given'45'cata'45'void_602 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'void_602 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_success_258 (coe MAlonzo.Code.Once.Type.C_Void_120)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Seq.du_seq0_34
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe v4)
                             (coe
                                MAlonzo.Code.Once.Surface.Seq.du_embedClosed_60
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0))
                                (coe v4) (coe v6))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_initial_76)))
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032 v4
                          v3))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_260 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_642 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'dec_642 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'dec_642 v2 v3 v4 v5 v6 v7 v8 v9
du_embedOrSubsume'45'dec_642 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'dec_642 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_112 (coe v0)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_378 v2 v10 v3)
                              (coe v4) (coe v5))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_736 v2 v6 v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_114
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v1)
                             (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume_684 ~v0 ~v1 v2 v3 = du_embedOrSubsume_684 v2 v3
du_embedOrSubsume_684 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume_684 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_embedOrSubsume'45'dec_642 (coe v5) (coe v0) (coe v4) (coe v6)
                    (coe v7) (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374 (coe v4) (coe v0))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_714 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specId_714 ~v0 = du_specId_714
du_specId_714 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specId_714
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_722 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specFst_722 ~v0 ~v1 = du_specFst_722
du_specFst_722 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specFst_722
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_732 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specSnd_732 ~v0 ~v1 = du_specSnd_732
du_specSnd_732 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specSnd_732
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_742 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInl_742 ~v0 ~v1 = du_specInl_742
du_specInl_742 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInl_742
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_752 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInr_752 ~v0 ~v1 = du_specInr_752
du_specInr_752 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInr_752
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_758 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specUnitGen_758 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
-- Once.TypeCheck.Elaborate.specPair
d_specPair_766 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specPair_766 v0 ~v1 ~v2 = du_specPair_766 v0
du_specPair_766 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specPair_766 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6)))
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_pair_78
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_776 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specTerminal_776 ~v0 = du_specTerminal_776
du_specTerminal_776 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specTerminal_776
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_782 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInitial_782 ~v0 = du_specInitial_782
du_specInitial_782 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInitial_782
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_792 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCurry_792 v0 v1 ~v2 = du_specCurry_792 v0 v1
du_specCurry_792 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCurry_792 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_50
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_78
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_804 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specApply_804 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_50
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))
         v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_102
            (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_816 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCompose_816 v0 v1 ~v2 = du_specCompose_816 v0 v1
du_specCompose_816 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCompose_816 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_50
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specCase
d_specCase_830 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCase_830 v0 v1 ~v2 = du_specCase_830 v0 v1
du_specCase_830 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCase_830 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_Zero_6)
         (coe
            MAlonzo.Code.Once.Type.d__'8852'q__24
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'8852'q__24
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'8852'q__24
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_case''_148
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               v0 v1
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.extract-morph-aux
d_extract'45'morph'45'aux_854 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph'45'aux_854 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_extract'45'morph'45'aux_854 v3 v7
du_extract'45'morph'45'aux_854 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_854 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_872 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_872 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_extract'45'morph_872 v3 v4 v5 v6
du_extract'45'morph_872 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_872 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_854
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_878 a0 = ()
data T_WellFormedFView_878
  = C_wfv'45'yes_884 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 |
    C_wfv'45'no_886
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_890 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> T_WellFormedFView_878
d_inspectWellFormedF_890 v0
  = let v1
          = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe C_wfv'45'yes_884 v2
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_886
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_906 = ()
data T_AppSpine_906
  = C_mkSpine_916 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_912 ::
  T_AppSpine_906 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_912 v0
  = case coe v0 of
      C_mkSpine_916 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_914 ::
  T_AppSpine_906 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_914 v0
  = case coe v0 of
      C_mkSpine_916 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_918 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_906
d_spineOf_918 v0
  = coe
      du_go_926 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_926 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_906
d_go_926 ~v0 v1 v2 = du_go_926 v1 v2
du_go_926 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_906
du_go_926 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_go_926 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe
             C_mkSpine_916
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe C_mkSpine_916 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_1026 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_1026 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("compose" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("id" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.matchInferResult
d_matchInferResult_1034 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
d_matchInferResult_1034 ~v0 ~v1 v2 v3
  = du_matchInferResult_1034 v2 v3
du_matchInferResult_1034 ::
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
du_matchInferResult_1034 v0 v1
  = case coe v0 of
      C_success_88 v2 v3 v4 v5 v6
        -> let v7
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v1) (coe v2) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe C_success_112 (coe v3) (coe v4) (coe v5) (coe v6))
                       else coe
                              seq (coe v9)
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_90 v2 -> coe C_failure_114 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1082 a0 a1 = ()
data T_FunProjection_1082
  = C_isFun_1096 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_isEff_1104 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notFun_1106 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1112 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_FunProjection_1082
d_asFun_1112 ~v0 ~v1 v2 = du_asFun_1112 v2
du_asFun_1112 :: T_InferElabResult_74 -> T_FunProjection_1082
du_asFun_1112 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  C_isFun_1096 (coe v6) (coe v9) (coe v8) (coe v2) (coe v3) (coe v4)
                                  (coe v5)
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         C_notFun_1106
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         C_notFun_1106
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         C_isEff_1104 (coe v6) (coe v8) (coe v2) (coe v3) (coe v4)
                                         (coe v5)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notFun_1106
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notFun_1106 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1180 a0 a1 = ()
data T_IntProjection_1180
  = C_isInt_1188 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notInt_1190 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1196 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_IntProjection_1180
d_asInt_1196 ~v0 ~v1 v2 = du_asInt_1196 v2
du_asInt_1196 :: T_InferElabResult_74 -> T_IntProjection_1180
du_asInt_1196 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe C_isInt_1188 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notInt_1190
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notInt_1190 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1232 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1232 ~v0 ~v1 v2 = du_notNumeric_1232 v2
du_notNumeric_1232 ::
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1232 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1260 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1260 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased)
      MAlonzo.Code.Once.Type.C_One_8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Many_10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab-RApp-id
d_inferElab'45'RApp'45'id_1264 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  T_InferElabResult_74 -> T_InferElabResult_74
d_inferElab'45'RApp'45'id_1264 v0 v1
  = case coe v1 of
      C_success_88 v2 v3 v4 v5 v6
        -> coe
             C_success_88 (coe v2)
             (coe
                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_90 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bbc-other-poly-witness
d_bbc'45'other'45'poly'45'witness_1288
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.bbc-other-poly-witness"
-- Once.TypeCheck.Elaborate.bbc-other-poly-infer-witness
d_bbc'45'other'45'poly'45'infer'45'witness_1296
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.bbc-other-poly-infer-witness"
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_246 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 v0 v1 v2 v3
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_246 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88
                (coe MAlonzo.Code.Once.Type.d_extractGround_322 (coe v2) (coe v4))
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_404 v1)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
             (coe
                d_bbc'45'other'45'poly'45'infer'45'witness_1296 v0 v1
                (MAlonzo.Code.Once.Type.d_extractGround_322 (coe v2) (coe v4)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_failure_90
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 v0 v1 v2 ~v3
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1306 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.Type.d_isGround_442 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-aux
d_inferElabV'45'RVar'45'poly'45'aux_1346 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'aux_1346 v0 v1
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1328 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_14
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0))
         (coe v1))
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1354 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab_1354 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inferElabV_1606 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_1360 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
d_checkElab_1360 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_checkElabV_1614 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_1370 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPair_1370 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("pair" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("pair" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v15 of
                                                                                    MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                                                                                      -> let v20
                                                                                               = d_checkElabV_1614
                                                                                                   (coe
                                                                                                      v0)
                                                                                                   (coe
                                                                                                      v6)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v14)
                                                                                                      (coe
                                                                                                         v18)) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v20 of
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                -> case coe
                                                                                                          v21 of
                                                                                                     C_success_112 v23 v24 v25 v26
                                                                                                       -> let v27
                                                                                                                = d_checkElabV_1614
                                                                                                                    (coe
                                                                                                                       v0)
                                                                                                                    (coe
                                                                                                                       v2)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                       (coe
                                                                                                                          v13)
                                                                                                                       (coe
                                                                                                                          v14)
                                                                                                                       (coe
                                                                                                                          v19)) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v27 of
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                 -> case coe
                                                                                                                           v28 of
                                                                                                                      C_success_112 v30 v31 v32 v33
                                                                                                                        -> coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                             (coe
                                                                                                                                C_success_112
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                                                   (coe
                                                                                                                                      v23)
                                                                                                                                   (coe
                                                                                                                                      v30))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_fork''_482
                                                                                                                                   v23
                                                                                                                                   v30
                                                                                                                                   v24
                                                                                                                                   v31)
                                                                                                                                (coe
                                                                                                                                   addInt
                                                                                                                                   (coe
                                                                                                                                      (1 ::
                                                                                                                                         Integer))
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                      (coe
                                                                                                                                         v25)
                                                                                                                                      (coe
                                                                                                                                         v32)))
                                                                                                                                (coe
                                                                                                                                   v33))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_680
                                                                                                                                v23
                                                                                                                                v30
                                                                                                                                v22
                                                                                                                                v29)
                                                                                                                      C_failure_114 v30
                                                                                                                        -> coe
                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                             (coe
                                                                                                                                v28)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                     C_failure_114 v23
                                                                                                       -> coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               v21)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                    _ -> coe v4
                                                                             _ -> coe v4
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_1382 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairLit_1382 v0 v1 v2 v3 v4
  = let v5 = d_checkElabV_1614 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                C_success_112 v8 v9 v10 v11
                  -> let v12 = d_checkElabV_1614 (coe v0) (coe v2) (coe v4) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 C_success_112 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_112
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                              (coe v8) (coe v15))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v8 v15 v9
                                              v16)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_772
                                           v8 v15 v7 v14)
                                 C_failure_114 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_114 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCase
d_checkCase_1392 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCase_1392 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("case" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("case" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C__'43'__124 v16 v17
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                                                               -> case coe v18 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> coe
                                                                                           d_checkCaseGo_1408
                                                                                           (coe v0)
                                                                                           (coe v6)
                                                                                           (coe v2)
                                                                                           (coe v16)
                                                                                           (coe v17)
                                                                                           (coe v15)
                                                                                           (coe v19)
                                                                                    _ -> coe v4
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v4
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_1408 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseGo_1408 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_checkElabV_1614
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                 (coe v5)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                C_success_112 v10 v11 v12 v13
                  -> let v14
                           = d_checkElabV_1614
                               (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                                  (coe v5)) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> case coe v15 of
                                 C_success_112 v17 v18 v19 v20
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_112
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                              (coe v10) (coe v17))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_464 v10
                                              v17 v11 v18)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v12)
                                                 (coe v19)))
                                           (coe v13))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_660
                                           v10 v17 v9 v16)
                                 C_failure_114 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_114 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCompose
d_checkCompose_1418 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose_1418 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("compose" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("compose" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> coe
                                                                                    d_checkCompose'45'g_1464
                                                                                    (coe v0)
                                                                                    (coe v6)
                                                                                    (coe v2)
                                                                                    (coe v13)
                                                                                    (coe v15)
                                                                                    (coe v17)
                                                                                    (coe
                                                                                       d_elabGivenV_1428
                                                                                       (coe v0)
                                                                                       (coe v2)
                                                                                       (coe v13)
                                                                                       (coe v17))
                                                                             _ -> coe v4
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.elabGivenV
d_elabGivenV_1428 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenV_1428 v0 v1 v2 v3
  = let v4
          = coe
              du_given'45'infer_418 (coe v2) (coe v3)
              (coe d_inferElabV_1606 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v5
           -> coe
                du_elabGivenLeaf_1438 (coe v0) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_788
                   (coe v1))
                (coe d_inferElabV_1606 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> coe
                d_elabGivenApp_1450 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_788
                   (coe v5))
                (coe d_inferElabV_1606 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v5 v6
           -> let v7
                    = d_inferElabV_1606
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                           (coe v5) (coe v2))
                        (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v8 of
                          C_success_88 v10 v11 v12 v13 v14
                            -> case coe v11 of
                                 MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v17
                                   -> let v18
                                            = d_decideLeq_1260
                                                (coe v16) (coe MAlonzo.Code.Once.Type.C_Many_10) in
                                      coe
                                        (case coe v18 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_success_258 (coe v10) (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                        v16 v12)
                                                     (coe addInt (coe (1 :: Integer)) (coe v13))
                                                     (coe v14))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878
                                                     v16 v9)
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_260
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                                        (coe v5)
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe v16)))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_failure_90 v10
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_failure_260 (coe v10))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_1438 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenLeaf_1438 v0 ~v1 v2 v3 v4 v5
  = du_elabGivenLeaf_1438 v0 v2 v3 v4 v5
du_elabGivenLeaf_1438 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elabGivenLeaf_1438 v0 v1 v2 v3 v4
  = let v5 = coe du_given'45'infer_418 (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_744
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_success_258 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                      (coe MAlonzo.Code.Once.IR.C_id_20))
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_746
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("fst" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C_Void_120
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998)
                   MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_fst_42))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916)
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_748
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("snd" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C_Void_120
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004)
                   MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926)
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_750
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_success_258 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                      (coe MAlonzo.Code.Once.IR.C_terminal_72))
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_756
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("initial" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C_Void_120
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940)
                   _ -> coe v6)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.elabGivenApp
d_elabGivenApp_1450 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenApp_1450 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe du_given'45'infer_418 (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_764
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                              (coe ("cata" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Type.C_Void_120
                     -> coe
                          du_given'45'cata'45'void_602 (coe v0)
                          (coe
                             d_inferElabV_1606
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                             (coe v2))
                   MAlonzo.Code.Once.Type.C_μ'45'type_128 v9
                     -> let v10
                              = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> coe
                                    du_given'45'cata_548 (coe v0) (coe v9) (coe v4) (coe v11)
                                    (coe
                                       d_inferElabV_1606
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                             (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                             (coe v0)))
                                       (coe v2))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       C_failure_260
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                          (coe ("cata" :: Data.Text.Text))))
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_772
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_1428 (coe v0) (coe v10) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_1428
                                                (coe v0) (coe v2) (coe v3) (coe v4) in
                                      coe
                                        (case coe v19 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                             -> case coe v20 of
                                                  C_success_258 v22 v23 v24 v25 v26
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_success_258
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C__'42'__122
                                                               (coe v14) (coe v22))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                               (coe v15) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_fork''_482
                                                               v15 v23 v16 v24)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v17) (coe v25)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980
                                                            v15 v23 v13 v21)
                                                  C_failure_260 v22
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v20)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_260 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v7
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_776
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_1428 (coe v0) (coe v2) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_1428
                                                (coe v0) (coe v10) (coe v14) (coe v4) in
                                      coe
                                        (case coe v19 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                             -> case coe v20 of
                                                  C_success_258 v22 v23 v24 v25 v26
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_success_258 (coe v22)
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                               (coe v23)
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                  (coe v15)))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_comp''_446
                                                               v23 v15 v14 v24 v16)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v25) (coe v17)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898
                                                            v14 v23 v15 v13 v21)
                                                  C_failure_260 v22
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v20)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_260 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v7
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_780
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_failure_260
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                     (coe ("case" :: Data.Text.Text))))
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Once.Type.C_Void_120
                            -> let v12
                                     = d_elabGivenV_1428 (coe v0) (coe v10) (coe v3) (coe v4) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           C_success_258 v15 v16 v17 v18 v19
                                             -> let v20
                                                      = d_elabGivenV_1428
                                                          (coe v0) (coe v2) (coe v3) (coe v4) in
                                                coe
                                                  (case coe v20 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                       -> case coe v21 of
                                                            C_success_258 v23 v24 v25 v26 v27
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_success_258 (coe v3)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                         (coe v16) (coe v24))
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                                         (coe v16) (coe v24)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v3)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v4))
                                                                            (coe v15))
                                                                         (coe v17)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Seq.du_seq0_34
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                               (coe v0))
                                                                            (coe v24)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                               (coe v3)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe v4))
                                                                               (coe v23))
                                                                            (coe v25)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IR.C_initial_76))))
                                                                      (coe
                                                                         addInt (coe (1 :: Integer))
                                                                         (coe
                                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                            (coe v18) (coe v26)))
                                                                      (coe v27))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022
                                                                      v15 v23 v16 v24 v14 v22)
                                                            C_failure_260 v23
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v21)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           C_failure_260 v15
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v13)
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                            -> let v14
                                     = d_elabGivenV_1428 (coe v0) (coe v10) (coe v12) (coe v4) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> case coe v15 of
                                           C_success_258 v17 v18 v19 v20 v21
                                             -> let v22
                                                      = d_elabGivenV_1428
                                                          (coe v0) (coe v2) (coe v13) (coe v4) in
                                                coe
                                                  (case coe v22 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                       -> case coe v23 of
                                                            C_success_258 v25 v26 v27 v28 v29
                                                              -> let v30
                                                                       = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                           (coe v25) (coe v17) in
                                                                 coe
                                                                   (case coe v30 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                        -> if coe v31
                                                                             then coe
                                                                                    seq (coe v32)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          C_success_258
                                                                                          (coe v25)
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                             (coe
                                                                                                v18)
                                                                                             (coe
                                                                                                v26))
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_464
                                                                                             v18 v26
                                                                                             v19
                                                                                             v27)
                                                                                          (coe
                                                                                             addInt
                                                                                             (coe
                                                                                                (1 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                (coe
                                                                                                   v20)
                                                                                                (coe
                                                                                                   v28)))
                                                                                          (coe v29))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960
                                                                                          v18 v26
                                                                                          v16 v24))
                                                                             else coe
                                                                                    seq (coe v32)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          C_failure_260
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                                             (coe
                                                                                                v17)
                                                                                             (coe
                                                                                                v25)))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            C_failure_260 v25
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           C_failure_260 v17
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v15)
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v11)
                _ -> coe v7
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.checkCompose-g
d_checkCompose'45'g_1464 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'g_1464 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v7 of
             C_success_258 v9 v10 v11 v12 v13
               -> let v14
                        = d_checkElabV_1614
                            (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                               (coe v4)) in
                  coe
                    (case coe v14 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                         -> case coe v15 of
                              C_success_112 v17 v18 v19 v20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_112
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe v17)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_446 v17 v10 v9
                                           v18 v11)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v19)
                                              (coe v12)))
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_616
                                        v9 v17 v10 v8 v16)
                              C_failure_114 v17
                                -> coe
                                     d_checkCompose'45'f_1478 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_260 v9
               -> coe
                    d_checkCompose'45'f_1478 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_1478 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'f_1478 v0 v1 v2 v3 v4 v5
  = let v6 = d_inferElabV_1606 (coe v0) (coe v1) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> let v9
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v7 of
                   C_success_88 v10 v11 v12 v13 v14
                     -> case coe v10 of
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                            -> case coe v16 of
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.Type.C_Many_10
                                          -> let v20
                                                   = coe
                                                       MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_256
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
                                                          (coe v15) (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
                                                          (coe v17) (coe v4))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__18
                                                          (coe v19) (coe v5)) in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                    -> if coe v21
                                                         then case coe v22 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                  -> let v24
                                                                           = d_checkElabV_1614
                                                                               (coe v0) (coe v2)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                  (coe v3)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                     (coe v18)
                                                                                     (coe v5))
                                                                                  (coe v15)) in
                                                                     coe
                                                                       (case coe v24 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                            -> case coe v25 of
                                                                                 C_success_112 v27 v28 v29 v30
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           C_success_112
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                              (coe
                                                                                                 v11)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                 (coe
                                                                                                    v18)
                                                                                                 (coe
                                                                                                    v27)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_446
                                                                                              v11
                                                                                              v27
                                                                                              v15
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                                                                                 v10
                                                                                                 v23
                                                                                                 v12)
                                                                                              v28)
                                                                                           (coe
                                                                                              addInt
                                                                                              (coe
                                                                                                 (1 ::
                                                                                                    Integer))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                 (coe
                                                                                                    v13)
                                                                                                 (coe
                                                                                                    v29)))
                                                                                           (coe
                                                                                              v30))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_640
                                                                                           v15 v17
                                                                                           v19 v11
                                                                                           v27 v8
                                                                                           v23 v26)
                                                                                 C_failure_114 v27
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v25)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         else coe
                                                                seq (coe v22)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_114
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v9
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v9
                   _ -> coe v9)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_1486 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurry_1486 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("curry" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v6 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                                       -> case coe v12 of
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> let v14
                                                       = d_checkElabV_1614
                                                           (coe v0) (coe v1)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C__'42'__122
                                                                 (coe v4) (coe v9))
                                                              (coe v10) (coe v11)) in
                                                 coe
                                                   (case coe v14 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                        -> case coe v15 of
                                                             C_success_112 v17 v18 v19 v20
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_112 (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_curry''_500
                                                                          v18)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v19))
                                                                       (coe v20))
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_698
                                                                       v16)
                                                             C_failure_114 v17
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v15)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> coe v3
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v3
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_1494 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkApply_1494 v0 v1 v2
  = let v3 = d_inferElabV_1606 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                C_success_88 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Unit_118
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Void_120
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_Zero_6
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("apply" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Type.C_One_8
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("apply" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                     -> let v18
                                                              = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                  (coe v13) (coe v12) in
                                                        coe
                                                          (let v19
                                                                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                     (coe v2) (coe v15) in
                                                           coe
                                                             (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                  -> if coe v20
                                                                       then coe
                                                                              seq (coe v21)
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                   -> if coe v22
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v23)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     C_success_112
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              v7)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                                                                        v7
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              v13))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.IR.C_apply_90)
                                                                                                        v8)
                                                                                                     (coe
                                                                                                        addInt
                                                                                                        (coe
                                                                                                           (1 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           v9))
                                                                                                     (coe
                                                                                                        v10))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_794
                                                                                                     v13
                                                                                                     v7
                                                                                                     v5))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v23)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     C_failure_114
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                                                        (coe
                                                                                                           v2)
                                                                                                        (coe
                                                                                                           v15)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       else coe
                                                                              seq (coe v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    C_failure_114
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                       (coe
                                                                                          ("apply"
                                                                                           ::
                                                                                           Data.Text.Text))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   MAlonzo.Code.Once.Type.C_eff_36
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_114
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Int_132
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Float_134
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Str_136
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Buffer_138
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_90 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_114 (coe v6))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_1500 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_1500 v0 ~v1 v2 = du_outIR_1500 v0 v2
du_outIR_1500 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_1500 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_1506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOut_1506 v0 v1
  = let v2 = d_inferElabV_1606 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                C_success_88 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_118
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Void_120
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v6 v5
                                    (coe MAlonzo.Code.Once.IR.C_initial_76) v7)
                                 (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'void_518
                                 v6 v4)
                       MAlonzo.Code.Once.Type.C__'42'__122 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v10 v11
                         -> coe
                              du_inferOutGo_1528 (coe v0) (coe v10) (coe v11) (coe v6) (coe v7)
                              (coe v8) (coe v9) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v10))
                       MAlonzo.Code.Once.Type.C_Int_132
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Float_134
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Str_136
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Buffer_138
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                    (coe ("Out" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_90 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_1528 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutGo_1528 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inferOutGo_1528 v0 v2 v3 v4 v5 v6 v7 v8 v9
du_inferOutGo_1528 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutGo_1528 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1)
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v1) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v3
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v1) (coe v2))
                          (coe du_outIR_1500 (coe v1) (coe v9)) v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_356
                       v1 v3 v9 v7)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                          (coe MAlonzo.Code.Once.Type.C_Unit_118)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1)
                             (coe MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v1) (coe v2))))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v3
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v1) (coe v2))
                          (coe
                             MAlonzo.Code.Once.IR.C_curry_84
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                   (coe MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v1) (coe v2)))
                                (coe du_outIR_1500 (coe v1) (coe v9))
                                (coe MAlonzo.Code.Once.IR.C_fst_42)))
                          v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_368
                       v1 v3 v9 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_1536 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkIn_1536 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("In" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
           -> coe
                du_checkInGo_1546 (coe v0) (coe v1) (coe v4)
                (coe
                   MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v4))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_1546 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo_1546 v0 v1 v2 v3 ~v4 = du_checkInGo_1546 v0 v1 v2 v3
du_checkInGo_1546 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo_1546 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = d_checkElabV_1614
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2)
                        (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_112 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8
                                    (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                       (coe v2)
                                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_In_94
                                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                          (coe v2) (coe v4)))
                                    v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_782
                                 v8 v4 v7)
                       C_failure_114 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_1554 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCata_1554 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("cata" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_checkCataGo_1568 (coe v0) (coe v1) (coe v7) (coe v6)
                                     (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                        (coe v7))
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_1568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataGo_1568 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkCataGo_1568 v0 v1 v2 v3 v4 v5
du_checkCataGo_1568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkCataGo_1568 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_1614
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                        (coe
                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                        (coe v3)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> case coe v8 of
                       C_success_112 v10 v11 v12 v13
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_success_112
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_512 v6 v11)
                                    (coe addInt (coe (1 :: Integer)) (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_710 v6
                                    v9))
                       C_failure_114 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_1576 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAna_1576 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                    (coe ("ana" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v6 of
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v9 v10
                                -> coe
                                     du_checkAnaGo_1592 (coe v0) (coe v1) (coe v9) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                        (coe v9))
                              _ -> coe v3
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_1592 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaGo_1592 v0 v1 v2 v3 ~v4 v5 v6 ~v7
  = du_checkAnaGo_1592 v0 v1 v2 v3 v5 v6
du_checkAnaGo_1592 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkAnaGo_1592 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_1614
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_338
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0)))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                        (coe
                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2)
                           (coe v3))) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> case coe v8 of
                       C_success_112 v10 v11 v12 v13
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_success_112
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_526 v6 v11)
                                    (coe addInt (coe (1 :: Integer)) (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_724 v6
                                    v9))
                       C_failure_114 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_1600 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab'45'RApp'45'other_1600 v0 v1 v2
  = let v3
          = coe
              du_asFun_1112
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe d_inferElabV_1606 (coe v0) (coe v1))) in
    coe
      (case coe v3 of
         C_isFun_1096 v4 v5 v6 v7 v8 v9 v10
           -> let v11
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_checkElabV_1614 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v11 of
                   C_success_112 v12 v13 v14 v15
                     -> coe
                          C_success_88 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v5)
                                (coe v12)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_app_50 v7 v12 v4 v5 v8 v13)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9) (coe v14))
                          (coe v15)
                   C_failure_114 v12 -> coe C_failure_90 (coe v12)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_isEff_1104 v4 v5 v6 v7 v8 v9
           -> let v10
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_checkElabV_1614 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v10 of
                   C_success_112 v11 v12 v13 v14
                     -> coe
                          C_success_88
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_eff_36))
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v6)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v11)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v6 v11 v4 v7 v12)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                          (coe v14)
                   C_failure_114 v11 -> coe C_failure_90 (coe v11)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_notFun_1106 v4 -> coe C_failure_90 (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV
d_inferElabV_1606 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV_1606 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_1972 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_528 (coe v0)
                (coe v2))
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_398
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe
             du_inferElabV'45'RQualified'45'aux_1886 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_398
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("." :: Data.Text.Text) v2)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_2144 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1166 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_inferElabV'45'RApp'45'dispatch_2020 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_788
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_30))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe
             du_inferElabV'45'RLet'45'aux_1724 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabV_1606 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe
             du_inferElabV'45'RPair'45'aux_1638
             (coe d_inferElabV_1606 (coe v0) (coe v2))
             (coe d_inferElabV_1606 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RDestruct'45'aux_1760 (coe v0) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe d_inferElabV_1606 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v2)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe
             du_inferElabV'45'RFloat'45'aux_2194 (coe v0) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Str_136)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_str_192 v2)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe
             du_inferElabV'45'RAnnot'45'aux_1646 (coe v3)
             (coe d_checkElabV_1614 (coe v0) (coe v2) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe
             du_inferElabV'45'RBinOp'45'void_1704 (coe v2)
             (coe d_inferElabV_1606 (coe v0) (coe v3))
             (coe d_inferElabV_1606 (coe v0) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe d_inferElabV'45'neg'45'dispatch_1658 (coe v0) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV
d_checkElabV_1614 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV_1614 v0 v1 v2
  = coe du_checkElabV'45'wf_1622 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-wf
d_checkElabV'45'wf_1622 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'wf_1622 v0 ~v1 v2 v3
  = du_checkElabV'45'wf_1622 v0 v2 v3
du_checkElabV'45'wf_1622 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'wf_1622 v0 v1 v2
  = let v3
          = coe
              du_embedOrSubsume_684 (coe v2)
              (coe d_inferElabV_1606 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_1972 (coe v0) (coe v4)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_528 (coe v0)
                           (coe v4))
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_398
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                           (coe v4)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          C_success_88 v8 v9 v10 v11 v12
                            -> coe du_embedOrSubsume_684 (coe v2) (coe v5)
                          C_failure_90 v8
                            -> coe
                                 d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2160 (coe v0) (coe v4)
                                 (coe v2) (coe v5)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe
                du_checkElabV'45'RResolved'45'dispatch_2152 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1166 (coe v4))
                (coe d_inferElabV_1606 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> coe
                du_checkElabV'45'RApp'45'dispatch_2032 (coe v0) (coe v4) (coe v5)
                (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_788
                   (coe v4))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_32))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                            -> let v12
                                     = d_checkElabV_1614
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362
                                            (coe v0) (coe v4) (coe v7))
                                         (coe v5) (coe v9) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           C_success_112 v15 v16 v17 v18
                                             -> case coe v15 of
                                                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v21
                                                    -> let v22
                                                             = d_decideLeq_1260
                                                                 (coe v20) (coe v10) in
                                                       coe
                                                         (case coe v22 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_success_112 (coe v21)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                         v20 v16)
                                                                      (coe
                                                                         addInt (coe (1 :: Integer))
                                                                         (coe v17))
                                                                      (coe v18))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_756
                                                                      v20 v14)
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_114
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                                                         (coe v4) (coe v10)
                                                                         (coe v20)))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           C_failure_114 v15
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v13)
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v4 v5
           -> coe
                d_checkElabV'45'RPair'45'aux_2204 (coe v0) (coe v4) (coe v5)
                (coe v2) (coe d_classifyRPairTarget_54 (coe v2))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe d_checkElabV'45'RInt'45'aux_2168 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v4 v5 v6 v7
           -> coe
                du_checkElabV'45'RFloat'45'aux_2182 (coe v0) (coe v4) (coe v5)
                (coe v6) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_1672 (coe v0) (coe v5) (coe v2)
                (coe d_negOperandView_138 (coe v5))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_1630 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other_1630 v0 v1 v2
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_1996 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHead_1018
         (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_1638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RPair'45'aux_1638 ~v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RPair'45'aux_1638 v3 v4
du_inferElabV'45'RPair'45'aux_1638 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RPair'45'aux_1638 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v9 of
                           C_success_88 v11 v12 v13 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_88
                                     (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v4) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                        (coe v5) (coe v12))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v5 v12 v6 v13)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                        (coe v14))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v5 v12 v3
                                     v10)
                           C_failure_90 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RAnnot-aux
d_inferElabV'45'RAnnot'45'aux_1646 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RAnnot'45'aux_1646 ~v0 ~v1 v2 v3
  = du_inferElabV'45'RAnnot'45'aux_1646 v2 v3
du_inferElabV'45'RAnnot'45'aux_1646 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RAnnot'45'aux_1646 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_112 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_success_88 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v3)
             C_failure_114 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_90 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RUnaryOp-aux
d_inferElabV'45'RUnaryOp'45'aux_1652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RUnaryOp'45'aux_1652 ~v0 ~v1 v2
  = du_inferElabV'45'RUnaryOp'45'aux_1652 v2
du_inferElabV'45'RUnaryOp'45'aux_1652 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RUnaryOp'45'aux_1652 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_88 v3 v4 v5 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'void_426 v2)
                    MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v3) (coe v4)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_306 v5)
                              (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v2)
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_1658 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'dispatch_1658 v0 v1
  = coe
      d_inferElabV'45'neg'45'aux_1664 (coe v0) (coe v1)
      (coe d_negOperandView_138 (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_1664 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'aux_1664 v0 v1 v2
  = case coe v2 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_132)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_186
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Type.C_Float_134)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_200
                          (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                             (coe
                                MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v7) (coe v8)
                                (coe v9))))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_inferElabV'45'RUnaryOp'45'aux_1652
             (coe d_inferElabV_1606 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_1672 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'dispatch_1672 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_1680 (coe v0) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
               -> coe
                    du_checkElabV'45'neg'45'float'45'aux_1694 (coe v0) (coe v8)
                    (coe v9) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_embedOrSubsume_684 (coe v2)
             (coe
                du_inferElabV'45'RUnaryOp'45'aux_1652
                (coe d_inferElabV_1606 (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_1680 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'int'45'aux_1680 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
              (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) v6
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_int_186
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))))
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_736
                                 (coe MAlonzo.Code.Once.Type.C_Int_132)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30))
                                 v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v2)
                                (coe MAlonzo.Code.Once.Type.C_Int_132)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_1694 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'float'45'aux_1694 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'neg'45'float'45'aux_1694 v0 v1 v2 v3 v5
du_checkElabV'45'neg'45'float'45'aux_1694 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'neg'45'float'45'aux_1694 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
              (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                    (coe MAlonzo.Code.Once.Type.C_Float_134) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_200
                                       (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                          (coe
                                             MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v1)
                                             (coe v2) (coe v3)))))
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_736
                                 (coe MAlonzo.Code.Once.Type.C_Float_134)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156)
                                 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_134)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-void
d_inferElabV'45'RBinOp'45'void_1704 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'void_1704 ~v0 v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RBinOp'45'void_1704 v1 v4 v5
du_inferElabV'45'RBinOp'45'void_1704 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'void_1704 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RBinOp'45'aux_1714 (coe v0) (coe v1) (coe v2) in
           coe
             (case coe v3 of
                C_success_88 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Unit_118
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> case coe v13 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v14) (coe v6) (coe v8)
                                                         (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v16))
                                                      (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v14 v4 v12)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_Void_120
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'l_470
                                               v13 v14 v4 v12)
                                     C_failure_90 v13
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                  (coe v13)))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v13 of
                                     C_success_88 v15 v16 v17 v18 v19
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v15)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v16) (coe v6) (coe v8)
                                                         (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v18))
                                                      (coe v19))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v16 v4 v14)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v13 of
                                     C_success_88 v15 v16 v17 v18 v19
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v15)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v16) (coe v6) (coe v8)
                                                         (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v18))
                                                      (coe v19))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v16 v4 v14)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v14 of
                                     C_success_88 v16 v17 v18 v19 v20
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v17) (coe v6) (coe v8)
                                                         (coe v18))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v19))
                                                      (coe v20))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v17 v4 v15)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v11
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> case coe v12 of
                                     C_success_88 v14 v15 v16 v17 v18
                                       -> case coe v14 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v15) (coe v6) (coe v8)
                                                         (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v17))
                                                      (coe v18))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v15 v4 v13)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v11 v12
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v13 of
                                     C_success_88 v15 v16 v17 v18 v19
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v15)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v16) (coe v6) (coe v8)
                                                         (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v18))
                                                      (coe v19))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v16 v4 v14)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_Int_132
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> case coe v13 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v14) (coe v6) (coe v8)
                                                         (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v16))
                                                      (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v14 v4 v12)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_Float_134
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> case coe v13 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v14) (coe v6) (coe v8)
                                                         (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v16))
                                                      (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v14 v4 v12)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_Str_136
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> case coe v13 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v14) (coe v6) (coe v8)
                                                         (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v16))
                                                      (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v14 v4 v12)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_Buffer_138
                         -> case coe v2 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v11 of
                                     C_success_88 v13 v14 v15 v16 v17
                                       -> case coe v13 of
                                            MAlonzo.Code.Once.Type.C_Void_120
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_88 (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                         (coe v7) (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Seq.du_seq_18
                                                         (coe v7) (coe v14) (coe v6) (coe v8)
                                                         (coe v15))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                         (coe v9) (coe v16))
                                                      (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486
                                                      v6 v7 v14 v4 v12)
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_1714 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'aux_1714 ~v0 v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RBinOp'45'aux_1714 v1 v4 v5
du_inferElabV'45'RBinOp'45'aux_1714 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'aux_1714 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__122 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_118
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_130 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_132
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_add_210
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_sub_220
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mul_230
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_div_288
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mod''_298
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lt_316
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_le_326
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_gt_336
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ge_346
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_eq_356
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ne_366
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276
                                                          v6 v13 v4 v11)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_134
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_240
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_250
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_260
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Str_136
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Buffer_138
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_118
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_130 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_132
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_240
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_250
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_260
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_278
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_134
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_240
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_250
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_260
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_270
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Str_136
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Buffer_138
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86 (coe v5)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_1724 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux_1724 v0 v1 ~v2 v3 v4
  = du_inferElabV'45'RLet'45'aux_1724 v0 v1 v3 v4
du_inferElabV'45'RLet'45'aux_1724 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux_1724 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe
                    du_inferElabV'45'RLet'45'aux2_1746 (coe v6) (coe v7) (coe v8)
                    (coe v9) (coe v5)
                    (coe
                       d_inferElabV_1606
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                          (coe v1) (coe v6))
                       (coe v2))
             C_failure_90 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_1746 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux2_1746 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                  v9 v10
  = du_inferElabV'45'RLet'45'aux2_1746 v4 v5 v6 v7 v9 v10
du_inferElabV'45'RLet'45'aux2_1746 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux2_1746 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> case coe v9 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v14)
                                    (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v1 v15 v14 v0 v2 v10)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)))
                              (coe v12))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v0 v14 v1 v15
                              v4 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_1760 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'aux_1760 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferElabV'45'RDestruct'45'aux_1760 v0 v2 v3 v4 v5 v6
du_inferElabV'45'RDestruct'45'aux_1760 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'aux_1760 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           du_inferElabV'45'RDestruct'45'voidL_1780 (coe v0) (coe v3) (coe v4)
                           (coe v9) (coe v10) (coe v11) (coe v12) (coe v7)
                           (coe
                              d_inferElabV_1606
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                                 (coe v1) (coe v8))
                              (coe v2))
                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxL_1834 (coe v0) (coe v3) (coe v4)
                           (coe v13) (coe v14) (coe v9) (coe v10) (coe v11) (coe v7)
                           (coe
                              d_inferElabV_1606
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                                 (coe v1) (coe v13))
                              (coe v2))
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_52))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-voidL
d_inferElabV'45'RDestruct'45'voidL_1780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'voidL_1780 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                        v8 v9 v10 v11
  = du_inferElabV'45'RDestruct'45'voidL_1780
      v0 v4 v5 v6 v7 v8 v9 v10 v11
du_inferElabV'45'RDestruct'45'voidL_1780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'voidL_1780 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             C_success_88 v11 v12 v13 v14 v15
               -> case coe v12 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v17 v18
                      -> coe
                           du_inferElabV'45'RDestruct'45'voidR_1806 (coe v3) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v11) (coe v17) (coe v18) (coe v10)
                           (coe
                              d_inferElabV_1606
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                                 (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_120))
                              (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-voidR
d_inferElabV'45'RDestruct'45'voidR_1806 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'voidR_1806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                        v7 v8 v9 v10 v11 v12 v13 v14 v15
  = du_inferElabV'45'RDestruct'45'voidR_1806
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_inferElabV'45'RDestruct'45'voidR_1806 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'voidR_1806 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             C_success_88 v12 v13 v14 v15 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v19
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v0)
                              (coe v1) (coe v2) (coe v3))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'void_454 v5 v12
                              v6 v18 v7 v19 v4 v8 v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_1834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxL_1834 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       v8 v9 v10 ~v11 v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_1834
      v0 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inferElabV'45'RDestruct'45'auxL_1834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxL_1834 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             C_success_88 v12 v13 v14 v15 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v19
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxR_1876 (coe v3) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v8) (coe v12) (coe v18) (coe v19) (coe v14)
                           (coe v15) (coe v11)
                           (coe
                              d_inferElabV_1606
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362 (coe v0)
                                 (coe v1) (coe v4))
                              (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_1876 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxR_1876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7 v8 v9 v10 ~v11 v12 v13 v14 v15 v16 v17 ~v18 v19 v20
  = du_inferElabV'45'RDestruct'45'auxR_1876
      v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v19 v20
du_inferElabV'45'RDestruct'45'auxR_1876 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxR_1876 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
        -> case coe v13 of
             C_success_88 v15 v16 v17 v18 v19
               -> case coe v16 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v22
                      -> let v23
                               = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                   (coe v6) (coe v15) in
                         coe
                           (case coe v23 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                -> if coe v24
                                     then coe
                                            seq (coe v25)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_success_88 (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                     (coe v2)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                        (coe v8) (coe v22)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_case''_148
                                                     v2 v8 v22 v7 v21 v0 v1 v3 v9 v17)
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v4)
                                                        (coe addInt (coe (1 :: Integer)) (coe v10)))
                                                     (coe addInt (coe (1 :: Integer)) (coe v18)))
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206
                                                  v0 v1 v7 v21 v2 v8 v22 v5 v11 v14))
                                     else coe
                                            seq (coe v25)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_90
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_54))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-aux
d_inferElabV'45'RQualified'45'aux_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'aux_1886 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RQualified'45'aux_1886 v0 v1 v2 v3
du_inferElabV'45'RQualified'45'aux_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'aux_1886 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RQualified'45'value'45'aux_1946 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
                     (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_90 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RQualified'45'arrow'45'aux_1914 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                        (coe v8))
                                     (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_90 (coe v4))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v1)
                   (coe v2)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_1894 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'aux_1894 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'aux_1894 v0 v1 v2 v3
du_inferElabV'45'RResolved'45'aux_1894 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'aux_1894 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_1958 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
                     (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_90 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_1932 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                        (coe v8))
                                     (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_90 (coe v4))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe
                      MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-arrow-aux
d_inferElabV'45'RQualified'45'arrow'45'aux_1914 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'arrow'45'aux_1914 v0 v1 v2 v3 v4 v5
                                                ~v6 v7 ~v8 v9 ~v10 v11 ~v12
  = du_inferElabV'45'RQualified'45'arrow'45'aux_1914
      v0 v1 v2 v3 v4 v5 v7 v9 v11
du_inferElabV'45'RQualified'45'arrow'45'aux_1914 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'arrow'45'aux_1914 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                 (coe
                                    MAlonzo.Code.Once.IR.C_SigOp_130 (coe v3) (coe v4)
                                    (coe
                                       du_ext'45'arrow'45'info_2214 (coe v3) (coe v4) (coe v2)
                                       (coe v1) (coe v5) (coe v9) (coe v10))))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78
                              (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v9 v10)
                              v11)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_DishonestSigOpType_26
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v1))
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                    (coe v4))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("." :: Data.Text.Text) v1))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                             (coe v4))))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_1932 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'arrow'45'aux_1932 v0 v1 v2 v3 v4 v5
                                               ~v6 v7 ~v8 v9 ~v10 v11 ~v12
  = du_inferElabV'45'RResolved'45'arrow'45'aux_1932
      v0 v1 v2 v3 v4 v5 v7 v9 v11
du_inferElabV'45'RResolved'45'arrow'45'aux_1932 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'arrow'45'aux_1932 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                 (coe
                                    MAlonzo.Code.Once.IR.C_SigOp_130 (coe v3) (coe v4)
                                    (coe
                                       du_ext'45'resolved'45'info_2226 (coe v3) (coe v4) (coe v1)
                                       (coe v5) (coe v9) (coe v10))))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v2
                              (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v9 v10)
                              v11)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_DishonestSigOpType_26
                                 (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                    (coe v4))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                             (coe v4))))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-value-aux
d_inferElabV'45'RQualified'45'value'45'aux_1946 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'value'45'aux_1946 v0 v1 v2 v3 ~v4 v5
                                                ~v6 v7 ~v8
  = du_inferElabV'45'RQualified'45'value'45'aux_1946
      v0 v1 v2 v3 v5 v7
du_inferElabV'45'RQualified'45'value'45'aux_1946 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'value'45'aux_1946 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386
                          (MAlonzo.Code.Once.CanonicalName.d_bare_12
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("." :: Data.Text.Text) v1)))
                          v6)
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v6
                       v7)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_DishonestSigOpType_26
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("." :: Data.Text.Text) v1))
                          (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_1958 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'value'45'aux_1958 v0 v1 v2 v3 ~v4 v5
                                               ~v6 v7 ~v8
  = du_inferElabV'45'RResolved'45'value'45'aux_1958 v0 v1 v2 v3 v5 v7
du_inferElabV'45'RResolved'45'value'45'aux_1958 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'value'45'aux_1958 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386 v1 v6)
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v2
                       v6 v7)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_DishonestSigOpType_26
                          (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                          (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_1972 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'lookup'45'aux_1972 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RVar'45'lookup'45'aux_1972 v0 v1 v2 v4
du_inferElabV'45'RVar'45'lookup'45'aux_1972 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'lookup'45'aux_1972 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v5) (coe v7)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_536 (coe v8))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    du_inferElabV'45'RVar'45'import'45'value'45'aux_1986 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_48 (coe v1))
                    (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
                    (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_90 (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe d_inferElabV'45'RVar'45'poly'45'aux_1346 (coe v0) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-import-value-aux
d_inferElabV'45'RVar'45'import'45'value'45'aux_1986 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'import'45'value'45'aux_1986 v0 v1 ~v2 v3
                                                    ~v4 v5 ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RVar'45'import'45'value'45'aux_1986
      v0 v1 v3 v5 v7 v9
du_inferElabV'45'RVar'45'import'45'value'45'aux_1986 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'import'45'value'45'aux_1986 v0 v1 v2 v3 v4
                                                     v5
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_90
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v7)
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v2)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                              (coe v0)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_sigOp_386
                                           (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1)) v8)
                                        (coe (0 :: Integer))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94
                                        v8 v9)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_DishonestSigOpType_26
                                           (coe v1) (coe v2)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_90
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                                    (coe v1) (coe v2)))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_1996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_708 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other'45'aux_1996 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'other'45'aux_1996 v0 v1 v2 v3
du_inferElabV'45'RApp'45'other'45'aux_1996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_708 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'other'45'aux_1996 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe
                      ("unreachable: ahv-other \8658 classifyAppHead nothing"
                       ::
                       Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     du_inferElabV'45'RApp'45'void_2010 (coe v8) (coe v9) (coe v10)
                                     (coe v11) (coe v6) (coe d_inferElabV_1606 (coe v0) (coe v2))
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_pure_34
                                              -> let v17
                                                       = coe
                                                           du_checkElabV'45'wf_1622 (coe v0)
                                                           (coe v2) (coe v12) in
                                                 coe
                                                   (case coe v17 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                        -> case coe v18 of
                                                             C_success_112 v20 v21 v22 v23
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_88 (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                          (coe v8)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                             (coe v15) (coe v20)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_app_50
                                                                          v8 v20 v12 v15 v9 v21)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                          (coe v10) (coe v22))
                                                                       (coe v23))
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_386
                                                                       v12 v15 v8 v20 v6 v19)
                                                             C_failure_114 v20
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe C_failure_90 (coe v20))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_eff_36
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_90
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_90
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> let v17
                                                              = coe
                                                                  du_checkElabV'45'wf_1622 (coe v0)
                                                                  (coe v2) (coe v12) in
                                                        coe
                                                          (case coe v17 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                               -> case coe v18 of
                                                                    C_success_112 v20 v21 v22 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_88
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_Unit_118)
                                                                                 (coe v13)
                                                                                 (coe v14))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                    (coe v15)
                                                                                    (coe v20)))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_effApp_64
                                                                                 v8 v20 v12 v9 v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v10)
                                                                                 (coe v22))
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402
                                                                              v12 v8 v20 v6 v19)
                                                                    C_failure_114 v20
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_90
                                                                              (coe v20))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              du_inferSpine_2040 (coe v0) (coe v1)
                              (coe d_inferElabV_1606 (coe v0) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-void
d_inferElabV'45'RApp'45'void_2010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'void_2010 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_inferElabV'45'RApp'45'void_2010 v4 v5 v6 v7 v8 v9
du_inferElabV'45'RApp'45'void_2010 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'void_2010 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v0)
                       (coe v1) (coe v2) (coe v3))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'void_532 v8 v9
                       v4 v7)
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_2020 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'dispatch_2020 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'dispatch_2020 v0 v1 v2 v3
du_inferElabV'45'RApp'45'dispatch_2020 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'dispatch_2020 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_744
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_id_20) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v8 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_746
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app'45'void_494
                                        v8 v6)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_fst_42) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298
                                        v13 v8 v6)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_748
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app'45'void_502
                                        v8 v6)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_snd_48) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310
                                        v12 v8 v6)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_750
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_terminal_72) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v7
                                 v8 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_752
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_34))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_754
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_36))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_756
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_38))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_758
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_760
        -> let v4 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'void_510
                                        v8 v6)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> case coe v12 of
                                     MAlonzo.Code.Once.Type.C_Unit_118
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Void_120
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_90
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_90
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v18 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v19
                                                                     = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                         (coe v14) (coe v13) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                      -> if coe v20
                                                                           then coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_success_88
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                                                 (coe
                                                                                                    v0)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                              (coe
                                                                                                 v17)
                                                                                              (coe
                                                                                                 v8)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                                                           v8
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Type.C__'42'__122
                                                                                              (coe
                                                                                                 v12)
                                                                                              (coe
                                                                                                 v14))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.IR.C_apply_90)
                                                                                           v9)
                                                                                        (coe
                                                                                           addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v10))
                                                                                        (coe v11))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                                                                                        v14 v8 v6))
                                                                           else coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_failure_90
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                           (coe
                                                                                              ("apply"
                                                                                               ::
                                                                                               Data.Text.Text))))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          MAlonzo.Code.Once.Type.C_eff_36
                                                            -> let v19
                                                                     = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                         (coe v14) (coe v13) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                      -> if coe v20
                                                                           then coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_success_88
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Type.C_Unit_118)
                                                                                           (coe v15)
                                                                                           (coe
                                                                                              v16))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                                                 (coe
                                                                                                    v0)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                              (coe
                                                                                                 v17)
                                                                                              (coe
                                                                                                 v8)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                                                           v8
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Type.C__'42'__122
                                                                                              (coe
                                                                                                 v12)
                                                                                              (coe
                                                                                                 v14))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.IR.C_curry_84
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                          (coe
                                                                                                             v14))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                          (coe
                                                                                                             v16)))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                       (coe
                                                                                                          v14)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.IR.C_apply_90)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.IR.C_fst_42)))
                                                                                           v9)
                                                                                        (coe
                                                                                           addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v10))
                                                                                        (coe v11))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_344
                                                                                        v14 v8 v6))
                                                                           else coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_failure_90
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                           (coe
                                                                                              ("apply"
                                                                                               ::
                                                                                               Data.Text.Text))))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_ν'45'type_130 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Int_132
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Float_134
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Str_136
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Buffer_138
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_90
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_762
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_764
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'ana_766
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'Out_768
        -> coe d_inferOut_1506 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_772
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_776
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_780
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_784
        -> coe
             d_inferElabV'45'RApp'45'other_1630 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_2032 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'dispatch_2032 v0 v1 v2 v3 v4 ~v5
  = du_checkElabV'45'RApp'45'dispatch_2032 v0 v1 v2 v3 v4
du_checkElabV'45'RApp'45'dispatch_2032 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_742 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'dispatch_2032 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_744
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_88 (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_id_20) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286
                                         v9 v7) in
                            coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_746
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v8)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_initial_76)
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app'45'void_494
                                                v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v13)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_fst_42) v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298
                                                v14 v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v15))
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_44 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_748
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v8)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_initial_76)
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app'45'void_502
                                                v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_snd_48) v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310
                                                v13 v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v15))
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_46 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_750
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_terminal_72) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320
                                         v8 v9 v7) in
                            coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_752
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_1622 (coe v0) (coe v2) (coe v5) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v8 of
                              C_success_112 v10 v11 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_112
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v10
                                           v5 (coe MAlonzo.Code.Once.IR.C_inl_54) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_806
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_40))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_754
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_1622 (coe v0) (coe v2) (coe v6) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v8 of
                              C_success_112 v10 v11 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_112
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v10
                                           v6 (coe MAlonzo.Code.Once.IR.C_inr_60) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_818
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_42))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_756
        -> let v5
                 = coe
                     du_checkElabV'45'wf_1622 (coe v0) (coe v2)
                     (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_112 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428 v8
                                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                                    (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_828
                                 v8 v7)
                       C_failure_114 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_758
        -> coe d_checkCurry_1486 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_760
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v8)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_initial_76)
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'void_510
                                                v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_Unit_118
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Void_120
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v17))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v17))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> let v20
                                                              = seq
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        C_failure_90
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                           (coe
                                                                              ("apply"
                                                                               ::
                                                                               Data.Text.Text))))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                        coe
                                                          (case coe v20 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                               -> case coe v21 of
                                                                    C_success_88 v23 v24 v25 v26 v27
                                                                      -> coe
                                                                           du_embedOrSubsume_684
                                                                           (coe v3) (coe v20)
                                                                    C_failure_90 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_114
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> let v20
                                                              = seq
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        C_failure_90
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                           (coe
                                                                              ("apply"
                                                                               ::
                                                                               Data.Text.Text))))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                        coe
                                                          (case coe v20 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                               -> case coe v21 of
                                                                    C_success_88 v23 v24 v25 v26 v27
                                                                      -> coe
                                                                           du_embedOrSubsume_684
                                                                           (coe v3) (coe v20)
                                                                    C_failure_90 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_114
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v20
                                                                     = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                         (coe v15) (coe v14) in
                                                               coe
                                                                 (case coe v20 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                      -> if coe v21
                                                                           then let v23
                                                                                      = seq
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                C_success_88
                                                                                                (coe
                                                                                                   v17)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                                                         (coe
                                                                                                            v0)))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                      (coe
                                                                                                         v18)
                                                                                                      (coe
                                                                                                         v9)))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                                                                   v9
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v15))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.IR.C_apply_90)
                                                                                                   v10)
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (1 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v11))
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                                                                                                v15
                                                                                                v9
                                                                                                v7)) in
                                                                                coe
                                                                                  (case coe v23 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                       -> case coe
                                                                                                 v24 of
                                                                                            C_success_88 v26 v27 v28 v29 v30
                                                                                              -> coe
                                                                                                   du_embedOrSubsume_684
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v23)
                                                                                            C_failure_90 v26
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      C_failure_114
                                                                                                      (coe
                                                                                                         v26))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           else (let v23
                                                                                       = seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 C_failure_90
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                                    (coe
                                                                                                       ("apply"
                                                                                                        ::
                                                                                                        Data.Text.Text))))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                                 coe
                                                                                   (case coe v23 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                        -> case coe
                                                                                                  v24 of
                                                                                             C_success_88 v26 v27 v28 v29 v30
                                                                                               -> coe
                                                                                                    du_embedOrSubsume_684
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v23)
                                                                                             C_failure_90 v26
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       C_failure_114
                                                                                                       (coe
                                                                                                          v26))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          MAlonzo.Code.Once.Type.C_eff_36
                                                            -> let v20
                                                                     = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                                                         (coe v15) (coe v14) in
                                                               coe
                                                                 (case coe v20 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                      -> if coe v21
                                                                           then let v23
                                                                                      = seq
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                C_success_88
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C_Unit_118)
                                                                                                   (coe
                                                                                                      v16)
                                                                                                   (coe
                                                                                                      v17))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                                                                         (coe
                                                                                                            v0)))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                      (coe
                                                                                                         v18)
                                                                                                      (coe
                                                                                                         v9)))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                                                                   v9
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v15))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.IR.C_curry_84
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                                  (coe
                                                                                                                     v15))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                                  (coe
                                                                                                                     v17)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                                                                               (coe
                                                                                                                  v15)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.IR.C_apply_90)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.IR.C_fst_42)))
                                                                                                   v10)
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (1 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v11))
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_344
                                                                                                v15
                                                                                                v9
                                                                                                v7)) in
                                                                                coe
                                                                                  (case coe v23 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                       -> case coe
                                                                                                 v24 of
                                                                                            C_success_88 v26 v27 v28 v29 v30
                                                                                              -> coe
                                                                                                   du_embedOrSubsume_684
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v23)
                                                                                            C_failure_90 v26
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      C_failure_114
                                                                                                      (coe
                                                                                                         v26))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           else (let v23
                                                                                       = seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 C_failure_90
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                                    (coe
                                                                                                       ("apply"
                                                                                                        ::
                                                                                                        Data.Text.Text))))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                                 coe
                                                                                   (case coe v23 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                        -> case coe
                                                                                                  v24 of
                                                                                             C_success_88 v26 v27 v28 v29 v30
                                                                                               -> coe
                                                                                                    du_embedOrSubsume_684
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v23)
                                                                                             C_failure_90 v26
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       C_failure_114
                                                                                                       (coe
                                                                                                          v26))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                                       -> let v16
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v16))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_ν'45'type_130 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v17))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Int_132
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Float_134
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Str_136
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Buffer_138
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_114 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_762
        -> coe d_checkIn_1536 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_764
        -> coe d_checkCata_1554 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'ana_766
        -> coe d_checkAna_1576 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'Out_768
        -> let v5 = d_inferElabV_1606 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_88 (coe v8)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_428
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_initial_76)
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'void_518
                                                v9 v7) in
                                   coe (coe du_embedOrSubsume_684 (coe v3) (coe v13))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13 v14
                                -> let v15
                                         = coe
                                             du_inferOutGo_1528 (coe v0) (coe v13) (coe v14)
                                             (coe v9) (coe v10) (coe v11) (coe v12) (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                                (coe v13)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> case coe v16 of
                                               C_success_88 v18 v19 v20 v21 v22
                                                 -> coe du_embedOrSubsume_684 (coe v3) (coe v15)
                                               C_failure_90 v18
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe C_failure_114 (coe v18))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                             (coe ("Out" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_114 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_772
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkPair_1370 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("pair" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_776
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCompose_1418 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("compose" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_780
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCase_1392 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("case" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_784
        -> let v6
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_2020 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_788
                        (coe v1)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_88 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_684 (coe v3) (coe v6)
                       C_failure_90 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_2040 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSpine_2040 v0 v1 ~v2 ~v3 v4 = du_inferSpine_2040 v0 v1 v4
du_inferSpine_2040 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSpine_2040 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> let v10
                        = d_elabGivenV_1428
                            (coe v0) (coe v1) (coe v5)
                            (coe MAlonzo.Code.Once.Type.C_pure_34) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v11 of
                              C_success_258 v13 v14 v15 v16 v17
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_88 (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe v14)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_50 v14 v6 v5
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) v15 v7)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16)
                                              (coe v8)))
                                        (coe v17))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_418
                                        v5 v14 v6 v4 v12)
                              C_failure_260 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe C_failure_90 (coe v13))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_90 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_2048 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_2048 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_114 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_114 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> let v8
                               = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v3) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_success_112
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                     (coe MAlonzo.Code.Once.IR.C_id_20))
                                                  (coe (0 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_540))
                                     else coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_114
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_2056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_2056 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                          (coe v6) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_112
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_550))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_2064 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_2064 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                          (coe v7) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_112
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                            (coe MAlonzo.Code.Once.IR.C_snd_48))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_560))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_2072 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_2072 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_112
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                        (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_568)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_2080 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_2080 v0 v1
                                                              v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_112
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                        (coe MAlonzo.Code.Once.IR.C_initial_76))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_576)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_2088 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_2088 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                          (coe v3) (coe v8) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_112
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                            (coe MAlonzo.Code.Once.IR.C_inl_54))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_586))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_2096 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_2096 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                          (coe v3) (coe v9) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_112
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_416
                                                            (coe MAlonzo.Code.Once.IR.C_inr_60))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_596))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_2102 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_2102 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_2048 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_2108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_2108 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_2056 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_2114 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_2114 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_2064 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_2120 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_2120 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_2072
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_2126 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_2126 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_2080
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_2132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_2132 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_2088 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_2138 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_2138 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_684 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_2096 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_2144 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'dispatch_2144 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1116
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1126
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1128
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1130
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1134 v4
        -> coe
             du_inferElabV'45'RResolved'45'aux_1894 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_398
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326 (coe v0))
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_2152 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'dispatch_2152 v0 ~v1 v2 v3 v4
  = du_checkElabV'45'RResolved'45'dispatch_2152 v0 v2 v3 v4
du_checkElabV'45'RResolved'45'dispatch_2152 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RResolved'45'dispatch_2152 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1116
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_2102 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1118
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_2108 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1120
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_2114 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1122
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_2120 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1124
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_2126 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1126
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_2132 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1128
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_2138 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1130
        -> coe du_embedOrSubsume_684 (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1134 v5
        -> coe du_embedOrSubsume_684 (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2160 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2160 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_684 (coe v2) (coe v3)
             C_failure_90 v6
               -> let v7
                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_14
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328 (coe v0))
                            (coe v1) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_404 v1)
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                    (coe v0)))
                              (coe d_bbc'45'other'45'poly'45'witness_1288 v0 v1 v2)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v6))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_2168 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RInt'45'aux_2168 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_132)
                 (coe
                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v1)
                 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
              (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30) in
    coe (coe du_embedOrSubsume_684 (coe v2) (coe v3))
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_2182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RFloat'45'aux_2182 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'RFloat'45'aux_2182 v0 v1 v2 v3 v5
du_checkElabV'45'RFloat'45'aux_2182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RFloat'45'aux_2182 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__374
              (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_112
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_378
                                    (coe MAlonzo.Code.Once.Type.C_Float_134) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_200
                                       (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                                          (coe v1) (coe v2) (coe v3))))
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_736
                                 (coe MAlonzo.Code.Once.Type.C_Float_134)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42) v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_134)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_2194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RFloat'45'aux_2194 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RFloat'45'aux_2194 v0 v1 v2 v3
du_inferElabV'45'RFloat'45'aux_2194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RFloat'45'aux_2194 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_success_88 (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_318 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_200
            (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
               (coe v1) (coe v2) (coe v3)))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324 (coe v0)))
      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42)
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_2204 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_RPairTarget_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RPair'45'aux_2204 v0 v1 v2 v3 v4
  = case coe v4 of
      C_rpt'45'prod_36
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
               -> coe
                    d_checkPairLit_1382 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_46
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_114
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                    (coe v11))
                                 (coe v11)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'other_50
        -> let v6
                 = coe
                     du_inferElabV'45'RPair'45'aux_1638
                     (coe d_inferElabV_1606 (coe v0) (coe v1))
                     (coe d_inferElabV_1606 (coe v0) (coe v2)) in
           coe (coe du_embedOrSubsume_684 (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-arrow-info
d_ext'45'arrow'45'info_2214 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162
d_ext'45'arrow'45'info_2214 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_ext'45'arrow'45'info_2214 v0 v1 v3 v4 v5 v6 v7
du_ext'45'arrow'45'info_2214 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162
du_ext'45'arrow'45'info_2214 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
             (coe
                MAlonzo.Code.Once.CanonicalName.d_bare_12
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("." :: Data.Text.Text) v3)))
             (coe
                MAlonzo.Code.Once.SigOp.Info.C_pureV_142
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_418 v0 v1
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v3))))
             (coe v5)
             (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154 (coe v6))
      MAlonzo.Code.Once.Type.C_eff_36
        -> let v7
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                     (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe
                                 MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
                                 (coe
                                    MAlonzo.Code.Once.CanonicalName.d_bare_12
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("." :: Data.Text.Text) v3)))
                                 (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_146) (coe v5)
                                 (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154 (coe v6)))
                       else coe
                              seq (coe v9)
                              (let v10
                                     = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                                         (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_118) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                      -> if coe v11
                                           then coe
                                                  seq (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
                                                     (coe
                                                        MAlonzo.Code.Once.CanonicalName.d_bare_12
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           v2
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              ("." :: Data.Text.Text) v3)))
                                                     (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_144)
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154
                                                        (coe v6)))
                                           else coe
                                                  seq (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
                                                     (coe
                                                        MAlonzo.Code.Once.CanonicalName.d_bare_12
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           v2
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              ("." :: Data.Text.Text) v3)))
                                                     (coe
                                                        MAlonzo.Code.Once.SigOp.Info.C_pureV_142
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_418
                                                           v0 v1
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              v2
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                 ("." :: Data.Text.Text) v3))))
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154
                                                        (coe v6)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info-aux
d_ext'45'resolved'45'info'45'aux_2220 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162
d_ext'45'resolved'45'info'45'aux_2220 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184 (coe v2)
             (coe
                MAlonzo.Code.Once.SigOp.Info.C_pureV_142
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_418 v0 v1
                   (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v2))))
             (coe v6)
             (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154 (coe v7))
      MAlonzo.Code.Once.Type.C_eff_36
        -> case coe v4 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
               -> if coe v8
                    then coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184 (coe v2)
                              (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_146) (coe v6)
                              (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154 (coe v7)))
                    else coe
                           seq (coe v9)
                           (case coe v5 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> if coe v10
                                     then coe
                                            seq (coe v11)
                                            (coe
                                               MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
                                               (coe v2)
                                               (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_144)
                                               (coe v6)
                                               (coe
                                                  MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154
                                                  (coe v7)))
                                     else coe
                                            seq (coe v11)
                                            (coe
                                               MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_184
                                               (coe v2)
                                               (coe
                                                  MAlonzo.Code.Once.SigOp.Info.C_pureV_142
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_418
                                                     v0 v1
                                                     (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134
                                                        (coe v2))))
                                               (coe v6)
                                               (coe
                                                  MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_154
                                                  (coe v7)))
                              _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info
d_ext'45'resolved'45'info_2226 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162
d_ext'45'resolved'45'info_2226 v0 v1 ~v2 v3 v4 v5 v6
  = du_ext'45'resolved'45'info_2226 v0 v1 v3 v4 v5 v6
du_ext'45'resolved'45'info_2226 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162
du_ext'45'resolved'45'info_2226 v0 v1 v2 v3 v4 v5
  = coe
      d_ext'45'resolved'45'info'45'aux_2220 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe MAlonzo.Code.Once.Type.d_isVoid'63'_160 (coe v1))
      (coe MAlonzo.Code.Once.Type.d_isUnit'63'_164 (coe v1)) (coe v4)
      (coe v5)
