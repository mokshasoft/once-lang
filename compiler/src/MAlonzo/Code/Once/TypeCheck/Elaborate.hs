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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
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
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Determined
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.TargetView
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
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Int_134
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
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Float_136
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
         MAlonzo.Code.Once.Type.C__'42'__124 v2 v3 -> coe C_rpt'45'prod_36
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C__'42'__124 v7 v8 -> coe C_rpt'45'vlift_46
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74 -> ()
d_soundOf_156 = erased
-- Once.TypeCheck.Elaborate.VerifiedInferResult
d_VerifiedInferResult_180 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_VerifiedInferResult_180 = erased
-- Once.TypeCheck.Elaborate.checkSoundOf
d_checkSoundOf_194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98 -> ()
d_checkSoundOf_194 = erased
-- Once.TypeCheck.Elaborate.VerifiedCheckResult
d_VerifiedCheckResult_222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> T_GivenElabResult_240 -> ()
d_givenSoundOf_270 = erased
-- Once.TypeCheck.Elaborate.VerifiedGivenResult
d_VerifiedGivenResult_306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> ()
d_VerifiedGivenResult_306 = erased
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_338 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                         (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v4))
                                                         (coe v2))
                                                      (coe
                                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                                         v14
                                                         (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                                                            (coe v2))
                                                         v17)
                                                      v6)
                                                   (coe v7) (coe v8))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_740
                                                   v1 v4 v9 v14 v17)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v16)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_260
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                     (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe v3))
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
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
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
                                (coe v2))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-infer
d_given'45'infer_418 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
                                  MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_80))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_Many_10
                                       -> coe
                                            du_given'45'infer'45'dec_338 (coe v0) (coe v11)
                                            (coe v13) (coe v1) (coe v15) (coe v6) (coe v7) (coe v8)
                                            (coe v9) (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                               (coe v0) (coe v11))
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
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
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_514 v1 v3)
                          (coe addInt (coe (1 :: Integer)) (coe v4))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_896 v1 v5))
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_260
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                             (coe ("cata" :: Data.Text.Text))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata_548 v0 ~v1 v2 v3 v4 v5
  = du_given'45'cata_548 v0 v2 v3 v4 v5
du_given'45'cata_548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
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
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                  (coe ("cata" :: Data.Text.Text))))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                         -> case coe v8 of
                              MAlonzo.Code.Once.Surface.Context.C_'91''93'_62
                                -> coe
                                     du_given'45'cata'45'dec_492 (coe v0) (coe v3) (coe v15)
                                     (coe v9) (coe v10) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                           (coe
                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v1)
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
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_610 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
d_embedOrSubsume'45'dec_610 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'dec_610 v2 v3 v4 v5 v6 v7 v8 v9
du_embedOrSubsume'45'dec_610 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'dec_610 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_112 (coe v0)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v2 v10 v3)
                              (coe v4) (coe v5))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_616 v2 v6 v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_114
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62 (coe v1)
                             (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume_652 ~v0 ~v1 v2 v3 = du_embedOrSubsume_652 v2 v3
du_embedOrSubsume_652 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume_652 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_embedOrSubsume'45'dec_610 (coe v5) (coe v0) (coe v4) (coe v6)
                    (coe v7) (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392 (coe v4) (coe v0))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_682 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specId_682 ~v0 = du_specId_682
du_specId_682 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specId_682
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_690 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specFst_690 ~v0 ~v1 = du_specFst_690
du_specFst_690 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specFst_690
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_700 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specSnd_700 ~v0 ~v1 = du_specSnd_700
du_specSnd_700 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specSnd_700
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_710 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInl_710 ~v0 ~v1 = du_specInl_710
du_specInl_710 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInl_710
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_720 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInr_720 ~v0 ~v1 = du_specInr_720
du_specInr_720 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInr_720
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_726 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specUnitGen_726 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
-- Once.TypeCheck.Elaborate.specPair
d_specPair_734 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specPair_734 v0 ~v1 ~v2 = du_specPair_734 v0
du_specPair_734 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specPair_734 v0
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
d_specTerminal_744 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specTerminal_744 ~v0 = du_specTerminal_744
du_specTerminal_744 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specTerminal_744
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_750 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInitial_750 ~v0 = du_specInitial_750
du_specInitial_750 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInitial_750
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_760 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCurry_760 v0 v1 ~v2 = du_specCurry_760 v0 v1
du_specCurry_760 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCurry_760 v0 v1
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
               (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v0) (coe v1))
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
d_specApply_772 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specApply_772 v0 v1
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
            (MAlonzo.Code.Once.Type.d__'8658'__150 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_784 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCompose_784 v0 v1 ~v2 = du_specCompose_784 v0 v1
du_specCompose_784 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCompose_784 v0 v1
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
d_specCase_798 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCase_798 v0 v1 ~v2 = du_specCase_798 v0 v1
du_specCase_798 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCase_798 v0 v1
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
d_extract'45'morph'45'aux_822 ::
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
d_extract'45'morph'45'aux_822 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_extract'45'morph'45'aux_822 v3 v7
du_extract'45'morph'45'aux_822 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_822 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_840 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_840 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_extract'45'morph_840 v3 v4 v5 v6
du_extract'45'morph_840 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_840 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_822
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v0)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_846 a0 = ()
data T_WellFormedFView_846
  = C_wfv'45'yes_852 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 |
    C_wfv'45'no_854
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_858 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> T_WellFormedFView_846
d_inspectWellFormedF_858 v0
  = let v1
          = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe C_wfv'45'yes_852 v2
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_854
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_874 = ()
data T_AppSpine_874
  = C_mkSpine_884 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_880 ::
  T_AppSpine_874 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_880 v0
  = case coe v0 of
      C_mkSpine_884 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_882 ::
  T_AppSpine_874 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_882 v0
  = case coe v0 of
      C_mkSpine_884 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_886 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_874
d_spineOf_886 v0
  = coe
      du_go_894 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_894 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_874
d_go_894 ~v0 v1 v2 = du_go_894 v1 v2
du_go_894 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_874
du_go_894 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_go_894 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe
             C_mkSpine_884
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe C_mkSpine_884 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_994 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_994 v0
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
d_matchInferResult_1002 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
d_matchInferResult_1002 ~v0 ~v1 v2 v3
  = du_matchInferResult_1002 v2 v3
du_matchInferResult_1002 ::
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
du_matchInferResult_1002 v0 v1
  = case coe v0 of
      C_success_88 v2 v3 v4 v5 v6
        -> let v7
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v2) in
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
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_90 v2 -> coe C_failure_114 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1050 a0 a1 = ()
data T_FunProjection_1050
  = C_isFun_1064 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_isEff_1072 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notFun_1074 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1080 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_FunProjection_1050
d_asFun_1080 ~v0 ~v1 v2 = du_asFun_1080 v2
du_asFun_1080 :: T_InferElabResult_74 -> T_FunProjection_1050
du_asFun_1080 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  C_isFun_1064 (coe v6) (coe v9) (coe v8) (coe v2) (coe v3) (coe v4)
                                  (coe v5)
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         C_notFun_1074
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         C_notFun_1074
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         C_isEff_1072 (coe v6) (coe v8) (coe v2) (coe v3) (coe v4)
                                         (coe v5)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    C_notFun_1074
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notFun_1074 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1150 a0 a1 = ()
data T_IntProjection_1150
  = C_isInt_1158 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notInt_1160 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1166 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_IntProjection_1150
d_asInt_1166 ~v0 ~v1 v2 = du_asInt_1166 v2
du_asInt_1166 :: T_InferElabResult_74 -> T_IntProjection_1150
du_asInt_1166 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe C_isInt_1158 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    C_notInt_1160
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notInt_1160 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1206 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1206 ~v0 ~v1 v2 = du_notNumeric_1206 v2
du_notNumeric_1206 ::
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1206 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1238 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1238 v0 v1
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
d_inferElab'45'RApp'45'id_1242 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  T_InferElabResult_74 -> T_InferElabResult_74
d_inferElab'45'RApp'45'id_1242 v0 v1
  = case coe v1 of
      C_success_88 v2 v3 v4 v5 v6
        -> coe
             C_success_88 (coe v2)
             (coe
                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_90 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_1262 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_1262 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_1304 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'k_1304 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19
  = du_given'45'poly'45'k_1304
      v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v19
du_given'45'poly'45'k_1304 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'k_1304 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
        -> if coe v15
             then case coe v16 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_258 (coe v3)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                                    (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2))
                                    (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v3))
                                    v13)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v1))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_764 v4 v6 v7 v8 v9
                              v10 v11 v12 v17 v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v16)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_260 (coe v5))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-π
d_given'45'poly'45'π_1388 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'π_1388 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16 v17 ~v18 v19
  = du_given'45'poly'45'π_1388
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v15 v16 v17 v19
du_given'45'poly'45'π_1388 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'π_1388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v13 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
        -> if coe v14
             then case coe v15 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                      -> coe
                           du_given'45'poly'45'k_1304 (coe v0) (coe v1) (coe v2)
                           (coe MAlonzo.Code.Once.Type.d_substPoly_562 (coe v12) (coe v6))
                           (coe v7) (coe v3) (coe v4) (coe v5) (coe v6) (coe v8) (coe v9)
                           (coe v10) (coe v11) (coe v16)
                           (coe
                              MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_658 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                                 (coe MAlonzo.Code.Once.Type.d_substPoly_562 (coe v12) (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v15)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_260 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-m
d_given'45'poly'45'm_1474 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'm_1474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16 v17 ~v18
  = du_given'45'poly'45'm_1474
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v15 v16 v17
du_given'45'poly'45'm_1474 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'm_1474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_given'45'poly'45'π_1388 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1596
                   (coe v6) (coe v2) (coe v14)))
             (coe
                MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22 (coe v8) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_260 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-d
d_given'45'poly'45'd_1550 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'd_1550 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16
  = du_given'45'poly'45'd_1550
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v15 v16
du_given'45'poly'45'd_1550 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'd_1550 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12
  = case coe v12 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then case coe v14 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                      -> coe
                           du_given'45'poly'45'm_1474 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                           (coe v11) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Type.Match.d_instantiate_100 (coe v6) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_260 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1612 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'a_1612 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
                          v12
  = du_given'45'poly'45'a_1612 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_given'45'poly'45'a_1612 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'a_1612 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v13 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  du_given'45'poly'45'd_1550 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v10) (coe v12) (coe v14) (coe v6) (coe v7)
                                  (coe v15)
                                  (coe
                                     MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_548
                                     (coe v10) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_260 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-g
d_given'45'poly'45'g_1676 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'g_1676 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
                          ~v12
  = du_given'45'poly'45'g_1676 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_given'45'poly'45'g_1676 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'g_1676 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_260 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             seq (coe v9)
             (coe
                du_given'45'poly'45'a_1612 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_566 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1736 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly_1736 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10
  = du_given'45'poly_1736 v0 v1 v2 v3 v4 v5 v7 v9
du_given'45'poly_1736 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly_1736 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_260 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_260 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                    -> coe
                                         du_given'45'poly'45'g_1676 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe v4) (coe v9) (coe v11) (coe v12)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_408 (coe v9))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_260 (coe v4))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-var
d_given'45'var_1798 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'var_1798 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             C_success_88 v7 v8 v9 v10 v11
               -> coe du_given'45'infer_418 (coe v2) (coe v3) (coe v4)
             C_failure_90 v7
               -> coe
                    du_given'45'poly_1736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_584 (coe v0)
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_144
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0))
                       (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-inst-aux
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834 v0 v1 ~v2 v3 v4 v5
                                                 v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834
      v0 v1 v3 v4 v5 v6 v11
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834 v0 v1 v2 v3 v4 v5
                                                  v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_112
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v1)
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_722
                              v3 v4 v5 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_114 (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-ground-aux
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886 v0 v1 v2 v3 v4
                                                   v5 v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886
      v0 v1 v2 v3 v4 v5 v6 v10
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886 v0 v1 v2 v3 v4
                                                    v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             seq (coe v8)
             (coe
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1834 (coe v0) (coe v1)
                (coe v3) (coe v4) (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_658 (coe v4)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1940 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1940 v0 v1 v2 v3 v4
                                                  ~v5 v6 ~v7 v8 ~v9
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_1940
      v0 v1 v2 v3 v4 v6 v8
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1940 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1940 v0 v1 v2 v3 v4
                                                   v5 v6
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v3))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> coe
                                         du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1886
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v10)
                                         (coe v11)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_408 (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_114 (coe v3))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996 v0 v1 ~v2 ~v3 v4
                                                   v5 ~v6 v7 ~v8
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996
      v0 v1 v4 v5 v7
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88
                (coe MAlonzo.Code.Once.Type.d_extractGround_326 (coe v2) (coe v5))
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v1)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104
                v2 v3
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.du_lookupPoly'8658'lookupPolyPrefix_322
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0))
                      (coe v1)))
                v5 v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_failure_90
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 v0 v1 ~v2 ~v3 v4
                                                   ~v5
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 v0 v1 v4
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1996 (coe v0)
                    (coe v1) (coe v4) (coe v5)
                    (coe MAlonzo.Code.Once.Type.d_isGround_408 (coe v4))
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
d_inferElabV'45'RVar'45'poly'45'aux_2062 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'aux_2062 v0 v1 ~v2 ~v3
  = du_inferElabV'45'RVar'45'poly'45'aux_2062 v0 v1
du_inferElabV'45'RVar'45'poly'45'aux_2062 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'aux_2062 v0 v1
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2034 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_22
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0))
         (coe v1))
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_2080 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenLeaf_2080 v0 ~v1 v2 v3 v4 v5
  = du_elabGivenLeaf_2080 v0 v2 v3 v4 v5
du_elabGivenLeaf_2080 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elabGivenLeaf_2080 v0 v1 v2 v3 v4
  = let v5 = coe du_given'45'infer_418 (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_800
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_success_258 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                      (coe MAlonzo.Code.Once.IR.C_id_20))
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_810)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_802
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                              (coe ("fst" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                (coe MAlonzo.Code.Once.IR.C_fst_42))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_820)
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_804
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                              (coe ("snd" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_830)
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_806
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_success_258 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                      (coe MAlonzo.Code.Once.IR.C_terminal_72))
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_838)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_812
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                              (coe ("initial" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v1 of
                   MAlonzo.Code.Once.Type.C_Void_122
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_258 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_844)
                   _ -> coe v6)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_2140 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_2140 v0 ~v1 v2 = du_outIR_2140 v0 v2
du_outIR_2140 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_2140 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_2170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutGo_2170 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inferOutGo_2170 v0 v2 v3 v4 v5 v6 v7 v8 v9
du_inferOutGo_2170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutGo_2170 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_pure_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v1)
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v1) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v3
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v1) (coe v2))
                          (coe du_outIR_2140 (coe v1) (coe v9)) v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350
                       v1 v3 v9 v7)
             MAlonzo.Code.Once.Type.C_eff_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                          (coe MAlonzo.Code.Once.Type.C_Unit_120)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v1)
                             (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v1) (coe v2))))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v3
                          (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v1) (coe v2))
                          (coe
                             MAlonzo.Code.Once.IR.C_curry_84
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                   (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v1) (coe v2)))
                                (coe du_outIR_2140 (coe v1) (coe v9))
                                (coe MAlonzo.Code.Once.IR.C_fst_42)))
                          v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362
                       v1 v3 v9 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutAt
d_inferOutAt_2244 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_206 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutAt_2244 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferOutAt_2244 v0 v2 v3 v4 v5 v6 v7 v8
du_inferOutAt_2244 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_206 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutAt_2244 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'at_212
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v10 v11
               -> coe
                    du_inferOutGo_2170 (coe v0) (coe v10) (coe v11) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'other_216
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutOn
d_inferOutOn_2282 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutOn_2282 v0 ~v1 v2 = du_inferOutOn_2282 v0 v2
du_inferOutOn_2282 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutOn_2282 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferOutAt_2244 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe MAlonzo.Code.Once.TypeCheck.TargetView.d_nuView_220 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstAt
d_inferFstAt_2320 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstAt_2320 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferFstAt_2320 v0 v2 v3 v4 v5 v6 v7 v8
du_inferFstAt_2320 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstAt_2320 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_260
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__124 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_fst_42) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v11 v2
                       v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_264
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_40))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstOn
d_inferFstOn_2358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstOn_2358 v0 ~v1 v2 = du_inferFstOn_2358 v0 v2
du_inferFstOn_2358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstOn_2358 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferFstAt_2320 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_prodView_268 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndAt
d_inferSndAt_2396 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndAt_2396 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferSndAt_2396 v0 v2 v3 v4 v5 v6 v7 v8
du_inferSndAt_2396 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndAt_2396 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_260
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__124 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                          (coe
                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_snd_48) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v10 v2
                       v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_264
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_42))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndOn
d_inferSndOn_2434 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndOn_2434 v0 ~v1 v2 = du_inferSndOn_2434 v0 v2
du_inferSndOn_2434 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndOn_2434 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferSndAt_2396 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_prodView_268 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyAt
d_inferApplyAt_2472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyAt_2472 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferApplyAt_2472 v0 v2 v3 v4 v5 v6 v7 v8
du_inferApplyAt_2472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyAt_2472 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'at_236
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__124 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> let v19
                                             = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                                C_success_88 (coe v16)
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                                         (coe v0)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v2)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430
                                                                   v2
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C__'42'__124
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                         (coe v14)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Many_10)
                                                                            (coe v18))
                                                                         (coe v16))
                                                                      (coe v14))
                                                                   (coe
                                                                      MAlonzo.Code.Once.IR.C_apply_90)
                                                                   v3)
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe v4))
                                                                (coe v5))
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326
                                                                v14 v2 v6))
                                                   else coe
                                                          seq (coe v21)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_90
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> let v19
                                             = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Unit_120)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v18))
                                                                   (coe v16))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                                         (coe v0)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v2)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430
                                                                   v2
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C__'42'__124
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                         (coe v14)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Many_10)
                                                                            (coe v18))
                                                                         (coe v16))
                                                                      (coe v14))
                                                                   (coe
                                                                      MAlonzo.Code.Once.IR.C_curry_84
                                                                      (coe
                                                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                                                         (coe
                                                                            MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                                  (coe v14))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                                  (coe v16)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                               (coe v14)))
                                                                         (coe
                                                                            MAlonzo.Code.Once.IR.C_apply_90)
                                                                         (coe
                                                                            MAlonzo.Code.Once.IR.C_fst_42)))
                                                                   v3)
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe v4))
                                                                (coe v5))
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338
                                                                v14 v2 v6))
                                                   else coe
                                                          seq (coe v21)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_90
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'other_240
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("apply" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyOn
d_inferApplyOn_2620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyOn_2620 v0 ~v1 v2 = du_inferApplyOn_2620 v0 v2
du_inferApplyOn_2620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyOn_2620 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferApplyAt_2472 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_applyView_244 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_2650 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RPair'45'aux_2650 ~v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RPair'45'aux_2650 v3 v4
du_inferElabV'45'RPair'45'aux_2650 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RPair'45'aux_2650 v0 v1
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
                                     (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v4) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                        (coe v5) (coe v12))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v5 v12 v6 v13)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                        (coe v14))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v5 v12 v3
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
d_inferElabV'45'RAnnot'45'aux_2704 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RAnnot'45'aux_2704 ~v0 ~v1 v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_2704 v2 v3 v4
du_inferElabV'45'RAnnot'45'aux_2704 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RAnnot'45'aux_2704 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v4 of
                    C_success_112 v6 v7 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_success_88 (coe v0) (coe v6) (coe v7) (coe v8) (coe v9))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v3 v5)
                    C_failure_114 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_90 (coe v6))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_AnnotationMentionsParameter_88
                   (coe v0)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RUnaryOp-aux
d_inferElabV'45'RUnaryOp'45'aux_2744 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RUnaryOp'45'aux_2744 ~v0 ~v1 v2
  = du_inferElabV'45'RUnaryOp'45'aux_2744 v2
du_inferElabV'45'RUnaryOp'45'aux_2744 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RUnaryOp'45'aux_2744 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_88 v3 v4 v5 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_Unit_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_122
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__124 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__126 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v3) (coe v4)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v5)
                              (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v2)
                    MAlonzo.Code.Once.Type.C_Float_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_rigid_138 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_2832 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'int'45'aux_2832 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v2) in
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
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) v6
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_int_186
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))))
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_616
                                 (coe MAlonzo.Code.Once.Type.C_Int_134)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138
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
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62 (coe v2)
                                (coe MAlonzo.Code.Once.Type.C_Int_134)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_2870 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'float'45'aux_2870 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'neg'45'float'45'aux_2870 v0 v1 v2 v3 v5
du_checkElabV'45'neg'45'float'45'aux_2870 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'neg'45'float'45'aux_2870 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) in
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
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                    (coe MAlonzo.Code.Once.Type.C_Float_136) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_194
                                       (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                          (coe
                                             MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v1)
                                             (coe v2) (coe v3)))))
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_616
                                 (coe MAlonzo.Code.Once.Type.C_Float_136)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150)
                                 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_2922 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'aux_2922 ~v0 v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RBinOp'45'aux_2922 v1 v4 v5
du_inferElabV'45'RBinOp'45'aux_2922 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'aux_2922 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Unit_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_122
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__126 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_134
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_122
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__126 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_132 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_134
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_add_204
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_sub_214
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mul_224
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_div_282
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mod''_292
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lt_310
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_le_320
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_gt_330
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ge_340
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_eq_350
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__126
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_120))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ne_360
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270
                                                          v6 v13 v4 v11)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_136
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_234
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_244
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_254
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_rigid_138 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Float_136
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_122
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__126 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_132 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_134
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_234
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_244
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_254
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_136
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_234
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_244
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_254
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228
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
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_134)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_rigid_138 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_84
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_rigid_138 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_82 (coe v5)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_3974 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
d_inferElabV'45'RLet'45'aux2_3974 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                  v9 v10
  = du_inferElabV'45'RLet'45'aux2_3974 v4 v5 v6 v7 v9 v10
du_inferElabV'45'RLet'45'aux2_3974 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux2_3974 v0 v1 v2 v3 v4 v5
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
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v0 v14 v1 v15
                              v4 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_4064 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
d_inferElabV'45'RDestruct'45'auxR_4064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7 v8 v9 v10 ~v11 v12 v13 v14 v15 v16 v17 ~v18 v19 v20
  = du_inferElabV'45'RDestruct'45'auxR_4064
      v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v19 v20
du_inferElabV'45'RDestruct'45'auxR_4064 ::
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
du_inferElabV'45'RDestruct'45'auxR_4064 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
        -> case coe v13 of
             C_success_88 v15 v16 v17 v18 v19
               -> case coe v16 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v22
                      -> let v23
                               = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200
                                                  v0 v1 v7 v21 v2 v8 v22 v5 v11 v14))
                                     else coe
                                            seq (coe v25)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_90
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_50))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-arrow-info
d_ext'45'arrow'45'info_4256 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_ext'45'arrow'45'info_4256 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_ext'45'arrow'45'info_4256 v1 v3 v4 v5 v6 v7
du_ext'45'arrow'45'info_4256 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_ext'45'arrow'45'info_4256 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
      (coe v0)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3))
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("." :: Data.Text.Text) v2)))
      (coe v4) (coe v5)
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-arrow-aux
d_inferElabV'45'RQualified'45'arrow'45'aux_4286 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'arrow'45'aux_4286 v0 v1 v2 v3 v4 v5
                                                ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RQualified'45'arrow'45'aux_4286
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RQualified'45'arrow'45'aux_4286 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'arrow'45'aux_4286 v0 v1 v2 v3 v4 v5
                                                 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                          (coe
                             MAlonzo.Code.Once.IR.C_SigOp_130 (coe v3) (coe v4)
                             (coe
                                du_ext'45'arrow'45'info_4256 (coe v4) (coe v2) (coe v1) (coe v5)
                                (coe v8) (coe v9))))
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72
                       (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v8 v9))
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
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
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
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-value-aux
d_inferElabV'45'RQualified'45'value'45'aux_4344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'value'45'aux_4344 v0 v1 v2 v3 ~v4 v5
                                                ~v6
  = du_inferElabV'45'RQualified'45'value'45'aux_4344 v0 v1 v2 v3 v5
du_inferElabV'45'RQualified'45'value'45'aux_4344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'value'45'aux_4344 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe v3)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                   (MAlonzo.Code.Once.CanonicalName.d_bare_12
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("." :: Data.Text.Text) v1)))
                   v5)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v5)
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
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-aux
d_inferElabV'45'RQualified'45'aux_4376 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'aux_4376 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RQualified'45'aux_4376 v0 v1 v2 v3
du_inferElabV'45'RQualified'45'aux_4376 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'aux_4376 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RQualified'45'value'45'aux_4344 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RQualified'45'arrow'45'aux_4286 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v8))
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
-- Once.TypeCheck.Elaborate.ext-resolved-sem
d_ext'45'resolved'45'sem_4412 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
d_ext'45'resolved'45'sem_4412 ~v0 ~v1 v2 v3 v4
  = du_ext'45'resolved'45'sem_4412 v2 v3 v4
du_ext'45'resolved'45'sem_4412 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_142
du_ext'45'resolved'45'sem_4412 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_150
      MAlonzo.Code.Once.Type.C_eff_36
        -> case coe v1 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
               -> if coe v3
                    then coe
                           seq (coe v4) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_156)
                    else coe
                           seq (coe v4)
                           (case coe v2 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> if coe v5
                                     then coe
                                            seq (coe v6)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_154)
                                     else coe
                                            seq (coe v6)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_152)
                              _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info-aux
d_ext'45'resolved'45'info'45'aux_4418 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_ext'45'resolved'45'info'45'aux_4418 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_ext'45'resolved'45'info'45'aux_4418 v2 v3 v4 v5 v6 v7
du_ext'45'resolved'45'info'45'aux_4418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_ext'45'resolved'45'info'45'aux_4418 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_186 (coe v0)
      (coe du_ext'45'resolved'45'sem_4412 (coe v1) (coe v2) (coe v3))
      (coe v4) (coe v5)
-- Once.TypeCheck.Elaborate.ext-resolved-info
d_ext'45'resolved'45'info_4436 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
d_ext'45'resolved'45'info_4436 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_ext'45'resolved'45'info_4436 v1 v3 v4 v5 v6
du_ext'45'resolved'45'info_4436 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164
du_ext'45'resolved'45'info_4436 v0 v1 v2 v3 v4
  = coe
      du_ext'45'resolved'45'info'45'aux_4418 (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Type.d_isVoid'63'_164 (coe v0))
      (coe MAlonzo.Code.Once.Type.d_isUnit'63'_168 (coe v0)) (coe v3)
      (coe v4)
-- Once.TypeCheck.Elaborate.resolvedArrowTerm
d_resolvedArrowTerm_4460 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvedArrowTerm_4460 v0 v1 ~v2 v3 v4 v5 v6
  = du_resolvedArrowTerm_4460 v0 v1 v3 v4 v5 v6
du_resolvedArrowTerm_4460 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvedArrowTerm_4460 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v6
        -> let v7
                 = coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                     (coe
                        MAlonzo.Code.Once.IR.C_SigOp_130 (coe v0) (coe v1)
                        (coe
                           du_ext'45'resolved'45'info_4436 (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5))) in
           coe
             (case coe v6 of
                (:) v8 v9
                  -> case coe v9 of
                       [] -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v8
                       _ -> coe v7
                _ -> coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_4496 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'arrow'45'aux_4496 v0 v1 v2 v3 v4 v5
                                               ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RResolved'45'arrow'45'aux_4496
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RResolved'45'arrow'45'aux_4496 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'arrow'45'aux_4496 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                       (coe
                          du_resolvedArrowTerm_4460 (coe v3) (coe v4) (coe v1) (coe v5)
                          (coe v8) (coe v9))
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v2
                       (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v8 v9))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
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
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.resolvedValueTerm
d_resolvedValueTerm_4550 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvedValueTerm_4550 ~v0 ~v1 ~v2 v3 v4
  = du_resolvedValueTerm_4550 v3 v4
du_resolvedValueTerm_4550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvedValueTerm_4550 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v2
        -> let v3
                 = coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v0 v1 in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v5 of
                       [] -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v4
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_4568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'value'45'aux_4568 v0 v1 v2 v3 ~v4 v5
                                               ~v6
  = du_inferElabV'45'RResolved'45'value'45'aux_4568 v0 v1 v2 v3 v5
du_inferElabV'45'RResolved'45'value'45'aux_4568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'value'45'aux_4568 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe v3)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe du_resolvedValueTerm_4550 (coe v1) (coe v5))
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v2
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_4598 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'aux_4598 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'aux_4598 v0 v1 v2 v3
du_inferElabV'45'RResolved'45'aux_4598 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'aux_4598 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_4568 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_4496 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v8))
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
                      MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-import-value-aux
d_inferElabV'45'RVar'45'import'45'value'45'aux_4640 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'import'45'value'45'aux_4640 v0 v1 ~v2 v3
                                                    ~v4 v5 ~v6 v7 ~v8
  = du_inferElabV'45'RVar'45'import'45'value'45'aux_4640
      v0 v1 v3 v5 v7
du_inferElabV'45'RVar'45'import'45'value'45'aux_4640 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'import'45'value'45'aux_4640 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_90
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v6)
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v1)
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v7)
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
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_4688 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'lookup'45'aux_4688 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RVar'45'lookup'45'aux_4688 v0 v1 v2 v4
du_inferElabV'45'RVar'45'lookup'45'aux_4688 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'lookup'45'aux_4688 v0 v1 v2 v3
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
                                 MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_538 (coe v8))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    du_inferElabV'45'RVar'45'import'45'value'45'aux_4640 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_54 (coe v1))
                    (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe du_inferElabV'45'RVar'45'poly'45'aux_2062 (coe v0) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4726 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
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
                               = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v3) (coe v5) in
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
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                                     (coe MAlonzo.Code.Once.IR.C_id_20))
                                                  (coe (0 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420))
                                     else coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_114
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4816 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4816 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
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
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4952 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4952 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
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
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                                            (coe MAlonzo.Code.Once.IR.C_snd_48))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5088 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5088 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
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
                           MAlonzo.Code.Once.Type.C_Unit_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_112
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                        (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448)
                           MAlonzo.Code.Once.Type.C_Void_122
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__124 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'43'__126 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_rigid_138 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5192 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5192 v0 v1
                                                              v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_122
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
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                        (coe MAlonzo.Code.Once.IR.C_initial_76))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_rigid_138 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5296 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5296 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
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
                           MAlonzo.Code.Once.Type.C__'43'__126 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                                            (coe MAlonzo.Code.Once.IR.C_inl_54))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_122
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__124 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_rigid_138 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5432 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5432 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
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
                           MAlonzo.Code.Once.Type.C__'43'__126 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                                                            (coe MAlonzo.Code.Once.IR.C_inr_60))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_122
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__124 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_rigid_138 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5566 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5566 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4726 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5584 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5584 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4816 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5602 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5602 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4952 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5620 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5088
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5638 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5192
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5656 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5656 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5296 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5674 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_652 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5432 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_5692 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1170 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'dispatch_5692 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1172
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1174
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1176
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1178
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1180
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1182
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1184
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1186
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1190 v4
        -> coe
             du_inferElabV'45'RResolved'45'aux_4598 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_5736 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1170 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'dispatch_5736 v0 ~v1 v2 v3 v4
  = du_checkElabV'45'RResolved'45'dispatch_5736 v0 v2 v3 v4
du_checkElabV'45'RResolved'45'dispatch_5736 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1170 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RResolved'45'dispatch_5736 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1172
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5566 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1174
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5584 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1176
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5602 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1178
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5620 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1180
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5638 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1182
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5656 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1184
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5674 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1186
        -> coe du_embedOrSubsume_652 (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1190 v5
        -> coe du_embedOrSubsume_652 (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_5802 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_5802 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_652 (coe v2) (coe v3)
             C_failure_90 v6
               -> coe
                    du_checkElabV'45'RVar'45'poly'45'check'45'aux_1940 (coe v0)
                    (coe v1) (coe v2) (coe v6)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_584 (coe v0)
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_144
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0))
                       (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_5832 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RFloat'45'aux_5832 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'RFloat'45'aux_5832 v0 v1 v2 v3 v5
du_checkElabV'45'RFloat'45'aux_5832 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RFloat'45'aux_5832 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) in
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
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                    (coe MAlonzo.Code.Once.Type.C_Float_136) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_194
                                       (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                                          (coe v1) (coe v2) (coe v3))))
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_616
                                 (coe MAlonzo.Code.Once.Type.C_Float_136)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42) v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_136)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_5886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RFloat'45'aux_5886 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RFloat'45'aux_5886 v0 v1 v2 v3
du_inferElabV'45'RFloat'45'aux_5886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RFloat'45'aux_5886 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_success_88 (coe MAlonzo.Code.Once.Type.C_Float_136)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_194
            (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
               (coe v1) (coe v2) (coe v3)))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_5906 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPair_5906 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
                                                          -> coe
                                                               d_checkPairOn_5916 (coe v0) (coe v6)
                                                               (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_pairTarget_124
                                                                  (coe v3))
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkPairOn
d_checkPairOn_5916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_106 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairOn_5916 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_116
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                      -> case coe v11 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v14 v15
                             -> let v16
                                      = d_checkElabV_6158
                                          (coe v0) (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v9)
                                             (coe
                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                             (coe v14)) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                       -> case coe v17 of
                                            C_success_112 v19 v20 v21 v22
                                              -> let v23
                                                       = d_checkElabV_6158
                                                           (coe v0) (coe v2)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                              (coe v9)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v13))
                                                              (coe v15)) in
                                                 coe
                                                   (case coe v23 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                        -> case coe v24 of
                                                             C_success_112 v26 v27 v28 v29
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_112
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                          (coe v19) (coe v26))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_fork''_484
                                                                          v19 v26 v20 v27)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                             (coe v21) (coe v28)))
                                                                       (coe v29))
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560
                                                                       v19 v26 v18 v25)
                                                             C_failure_114 v26
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v24)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            C_failure_114 v19
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v17)
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'other_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_5928 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairLit_5928 v0 v1 v2 v3 v4
  = let v5 = d_checkElabV_6158 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                C_success_112 v8 v9 v10 v11
                  -> let v12 = d_checkElabV_6158 (coe v0) (coe v2) (coe v4) in
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
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_652
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
d_checkCase_5938 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCase_5938 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
                                                          -> coe
                                                               d_checkCaseOn_5948 (coe v0) (coe v6)
                                                               (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_caseTarget_152
                                                                  (coe v3))
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCaseOn
d_checkCaseOn_5948 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_134 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseOn_5948 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_144
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v9 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                             -> coe
                                  d_checkCaseGo_5964 (coe v0) (coe v1) (coe v2) (coe v12) (coe v13)
                                  (coe v11) (coe v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'other_148
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_5964 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseGo_5964 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_checkElabV_6158
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
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
                           = d_checkElabV_6158
                               (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
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
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v10
                                              v17 v11 v18)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v12)
                                                 (coe v19)))
                                           (coe v13))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540
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
d_checkCompose_5974 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose_5974 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
                                                          -> coe
                                                               d_checkComposeOn_5984 (coe v0)
                                                               (coe v6) (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_arrowTarget_178
                                                                  (coe v3))
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkComposeOn
d_checkComposeOn_5984 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_162 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkComposeOn_5984 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_170
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v11 v12
                      -> coe
                           d_checkCompose'45'g_6020 (coe v0) (coe v1) (coe v2) (coe v8)
                           (coe v10) (coe v12)
                           (coe d_elabGivenV_5994 (coe v0) (coe v2) (coe v8) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_174
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.elabGivenV
d_elabGivenV_5994 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenV_5994 v0 v1 v2 v3
  = let v4
          = coe
              du_given'45'infer_418 (coe v2) (coe v3)
              (coe d_inferElabV_6150 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v5
           -> coe
                d_given'45'var_1798 (coe v0) (coe v5) (coe v2) (coe v3)
                (coe d_inferElabV_6150 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v5
           -> coe
                du_elabGivenLeaf_2080 (coe v0) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                   (coe v1))
                (coe d_inferElabV_6150 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> coe
                d_elabGivenApp_6006 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                   (coe v5))
                (coe d_inferElabV_6150 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v5 v6
           -> let v7
                    = d_inferElabV_6150
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
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
                                            = d_decideLeq_1238
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
                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_782
                                                     v16 v9)
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_260
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_74
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
-- Once.TypeCheck.Elaborate.elabGivenApp
d_elabGivenApp_6006 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenApp_6006 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe du_given'45'infer_418 (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_820
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                              (coe ("cata" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Type.C_μ'45'type_130 v9
                     -> let v10
                              = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> coe
                                    du_given'45'cata_548 (coe v0) (coe v9) (coe v4) (coe v11)
                                    (coe
                                       d_inferElabV_6150
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400
                                             (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402
                                             (coe v0)))
                                       (coe v2))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       C_failure_260
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                          (coe ("cata" :: Data.Text.Text))))
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_828
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_5994 (coe v0) (coe v10) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_5994
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
                                                               MAlonzo.Code.Once.Type.C__'42'__124
                                                               (coe v14) (coe v22))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                               (coe v15) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_fork''_484
                                                               v15 v23 v16 v24)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v17) (coe v25)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_884
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
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_832
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_5994 (coe v0) (coe v2) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_5994
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
                                                               MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
                                                               v23 v15 v14 v24 v16)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v25) (coe v17)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_802
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
         MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_836
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_failure_260
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                     (coe ("case" :: Data.Text.Text))))
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                            -> let v14
                                     = d_elabGivenV_5994 (coe v0) (coe v10) (coe v12) (coe v4) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> case coe v15 of
                                           C_success_258 v17 v18 v19 v20 v21
                                             -> let v22
                                                      = d_elabGivenV_5994
                                                          (coe v0) (coe v2) (coe v13) (coe v4) in
                                                coe
                                                  (case coe v22 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                       -> case coe v23 of
                                                            C_success_258 v25 v26 v27 v28 v29
                                                              -> let v30
                                                                       = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_466
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
                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_864
                                                                                          v18 v26
                                                                                          v16 v24))
                                                                             else coe
                                                                                    seq (coe v32)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          C_failure_260
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
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
d_checkCompose'45'g_6020 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'g_6020 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v7 of
             C_success_258 v9 v10 v11 v12 v13
               -> let v14
                        = d_checkElabV_6158
                            (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v9)
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
                                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v17 v10 v9
                                           v18 v11)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v19)
                                              (coe v12)))
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496
                                        v9 v17 v10 v8 v16)
                              C_failure_114 v17
                                -> coe
                                     d_checkCompose'45'f_6034 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_260 v9
               -> coe
                    d_checkCompose'45'f_6034 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_6034 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'f_6034 v0 v1 v2 v3 v4 v5
  = let v6 = d_inferElabV_6150 (coe v0) (coe v1) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> let v9
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_80))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v7 of
                   C_success_88 v10 v11 v12 v13 v14
                     -> case coe v10 of
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                            -> case coe v16 of
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.Type.C_Many_10
                                          -> let v20
                                                   = coe
                                                       MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_260
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                                          (coe v15) (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                                          (coe v17) (coe v4))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__22
                                                          (coe v19) (coe v5)) in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                    -> if coe v21
                                                         then case coe v22 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                  -> let v24
                                                                           = d_checkElabV_6158
                                                                               (coe v0) (coe v2)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
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
                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_448
                                                                                              v11
                                                                                              v27
                                                                                              v15
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
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
                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520
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
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_80))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v9
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v9
                   _ -> coe v9)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_6042 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurry_6042 v0 v1 v2
  = coe
      d_checkCurryOn_6050 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_curryTarget_94 (coe v2))
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_6050 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurryOn_6050 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'at_86
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v9 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> let v17
                                      = d_checkElabV_6158
                                          (coe v0) (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'42'__124 (coe v9)
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v16))
                                             (coe v14)) in
                                coe
                                  (case coe v17 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                       -> case coe v18 of
                                            C_success_112 v20 v21 v22 v23
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_success_112 (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_curry''_502
                                                         v21)
                                                      (coe addInt (coe (1 :: Integer)) (coe v22))
                                                      (coe v23))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578
                                                      v19)
                                            C_failure_114 v20
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v18)
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'other_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_6056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOut_6056 v0 v1
  = coe
      du_inferOutOn_2282 (coe v0)
      (coe d_inferElabV_6150 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_6064 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkIn_6064 v0 v1 v2
  = coe
      d_checkInOn_6072 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.TypeCheck.TargetView.d_inTarget_70 (coe v2))
-- Once.TypeCheck.Elaborate.checkInOn
d_checkInOn_6072 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_InTarget_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInOn_6072 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'at_62
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe
                    du_checkInGo_6082 (coe v0) (coe v1) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'other_66
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_6082 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo_6082 v0 v1 v2 v3 ~v4 = du_checkInGo_6082 v0 v1 v2 v3
du_checkInGo_6082 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo_6082 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = d_checkElabV_6158
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2)
                        (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v2))) in
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
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8
                                    (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                       (coe v2)
                                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_In_94
                                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                          (coe v2) (coe v4)))
                                    v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_662
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_6090 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCata_6090 v0 v1 v2
  = coe
      d_checkCataOn_6098 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_cataTarget_22 (coe v2))
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_6098 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataOn_6098 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v10
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v11 v12
                             -> coe
                                  du_checkCataGo_6112 (coe v0) (coe v1) (coe v10) (coe v9) (coe v12)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                     (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'other_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_6112 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataGo_6112 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkCataGo_6112 v0 v1 v2 v3 v4 v5
du_checkCataGo_6112 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkCataGo_6112 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_6158
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                        (coe
                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2) (coe v3))
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
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_514 v6 v11)
                                    (coe addInt (coe (1 :: Integer)) (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_590 v6
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_6120 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAna_6120 v0 v1 v2
  = coe
      d_checkAnaOn_6128 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_anaTarget_48 (coe v2))
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_6128 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaOn_6128 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'at_40
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v11 v12
                      -> coe
                           du_checkAnaGo_6144 (coe v0) (coe v1) (coe v11) (coe v8) (coe v12)
                           (coe
                              MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'other_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_6144 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaGo_6144 v0 v1 v2 v3 ~v4 v5 v6 ~v7
  = du_checkAnaGo_6144 v0 v1 v2 v3 v5 v6
du_checkAnaGo_6144 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkAnaGo_6144 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_6158
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                        (coe
                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2)
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
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_528 v6 v11)
                                    (coe addInt (coe (1 :: Integer)) (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_604 v6
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV
d_inferElabV_6150 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV_6150 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_4688 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_584 (coe v0)
                (coe v2))
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe
             du_inferElabV'45'RQualified'45'aux_4376 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("." :: Data.Text.Text) v2)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_5692 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1222 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_inferElabV'45'RApp'45'dispatch_6266 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_26))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe
             du_inferElabV'45'RLet'45'aux_6204 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabV_6150 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe
             du_inferElabV'45'RPair'45'aux_2650
             (coe d_inferElabV_6150 (coe v0) (coe v2))
             (coe d_inferElabV_6150 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RDestruct'45'aux_6218 (coe v0) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe d_inferElabV_6150 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v2)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe
             du_inferElabV'45'RFloat'45'aux_5886 (coe v0) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_StringLiteralUnsupported_24))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe
             du_inferElabV'45'RAnnot'45'aux_2704 (coe v3)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v3))
             (coe d_checkElabV_6158 (coe v0) (coe v2) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe
             du_inferElabV'45'RBinOp'45'aux_2922 (coe v2)
             (coe d_inferElabV_6150 (coe v0) (coe v3))
             (coe d_inferElabV_6150 (coe v0) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe d_inferElabV'45'neg'45'dispatch_6180 (coe v0) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV
d_checkElabV_6158 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV_6158 v0 v1 v2
  = coe du_checkElabV'45'wf_6166 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-wf
d_checkElabV'45'wf_6166 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'wf_6166 v0 ~v1 v2 v3
  = du_checkElabV'45'wf_6166 v0 v2 v3
du_checkElabV'45'wf_6166 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'wf_6166 v0 v1 v2
  = let v3
          = coe
              du_embedOrSubsume_652 (coe v2)
              (coe d_inferElabV_6150 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_4688 (coe v0) (coe v4)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_496
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0))
                           (coe v4)
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0)))
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                           (coe v4)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          C_success_88 v8 v9 v10 v11 v12
                            -> coe du_embedOrSubsume_652 (coe v2) (coe v5)
                          C_failure_90 v8
                            -> coe
                                 d_checkElabV'45'RVar'45'bbc'45'other'45'aux_5802 (coe v0) (coe v4)
                                 (coe v2) (coe v5)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe
                du_checkElabV'45'RResolved'45'dispatch_5736 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1222 (coe v4))
                (coe d_inferElabV_6150 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> coe
                du_checkElabV'45'RApp'45'dispatch_6278 (coe v0) (coe v4) (coe v5)
                (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                   (coe v4))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_28))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                            -> let v12
                                     = d_checkElabV_6158
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418
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
                                                             = d_decideLeq_1238
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
                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_636
                                                                      v20 v14)
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_114
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_74
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
                d_checkElabV'45'RPair'45'aux_6304 (coe v0) (coe v4) (coe v5)
                (coe v2) (coe d_classifyRPairTarget_54 (coe v2))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe d_checkElabV'45'RInt'45'aux_6294 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v4 v5 v6 v7
           -> coe
                du_checkElabV'45'RFloat'45'aux_5832 (coe v0) (coe v4) (coe v5)
                (coe v6) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_6194 (coe v0) (coe v5) (coe v2)
                (coe d_negOperandView_138 (coe v5))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_6174 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other_6174 v0 v1 v2
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_6256 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHead_1074
         (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_6180 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'dispatch_6180 v0 v1
  = coe
      d_inferElabV'45'neg'45'aux_6186 (coe v0) (coe v1)
      (coe d_negOperandView_138 (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_6186 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'aux_6186 v0 v1 v2
  = case coe v2 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_134)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_186
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_194
                          (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                             (coe
                                MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v7) (coe v8)
                                (coe v9))))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_inferElabV'45'RUnaryOp'45'aux_2744
             (coe d_inferElabV_6150 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_6194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'dispatch_6194 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_2832 (coe v0) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
               -> coe
                    du_checkElabV'45'neg'45'float'45'aux_2870 (coe v0) (coe v8)
                    (coe v9) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_embedOrSubsume_652 (coe v2)
             (coe
                du_inferElabV'45'RUnaryOp'45'aux_2744
                (coe d_inferElabV_6150 (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_6204 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux_6204 v0 v1 ~v2 v3 v4
  = du_inferElabV'45'RLet'45'aux_6204 v0 v1 v3 v4
du_inferElabV'45'RLet'45'aux_6204 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux_6204 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe
                    du_inferElabV'45'RLet'45'aux2_3974 (coe v6) (coe v7) (coe v8)
                    (coe v9) (coe v5)
                    (coe
                       d_inferElabV_6150
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                          (coe v1) (coe v6))
                       (coe v2))
             C_failure_90 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_6218 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'aux_6218 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferElabV'45'RDestruct'45'aux_6218 v0 v2 v3 v4 v5 v6
du_inferElabV'45'RDestruct'45'aux_6218 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'aux_6218 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_Unit_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_122
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxL_6246 (coe v0) (coe v3) (coe v4)
                           (coe v13) (coe v14) (coe v9) (coe v10) (coe v11) (coe v7)
                           (coe
                              d_inferElabV_6150
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                                 (coe v1) (coe v13))
                              (coe v2))
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Float_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_rigid_138 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_48))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_6246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
d_inferElabV'45'RDestruct'45'auxL_6246 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       v8 v9 v10 ~v11 v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_6246
      v0 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inferElabV'45'RDestruct'45'auxL_6246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
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
du_inferElabV'45'RDestruct'45'auxL_6246 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             C_success_88 v12 v13 v14 v15 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v19
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxR_4064 (coe v3) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v8) (coe v12) (coe v18) (coe v19) (coe v14)
                           (coe v15) (coe v11)
                           (coe
                              d_inferElabV_6150
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                                 (coe v1) (coe v4))
                              (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_6256 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_764 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other'45'aux_6256 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'other'45'aux_6256 v0 v1 v2 v3
du_inferElabV'45'RApp'45'other'45'aux_6256 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'other'45'aux_6256 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe
                      ("unreachable: ahv-other \8658 classifyAppHead nothing"
                       ::
                       Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v4 = d_inferElabV_6150 (coe v0) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_122
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_pure_34
                                              -> let v17
                                                       = coe
                                                           du_checkElabV'45'wf_6166 (coe v0)
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
                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380
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
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_90
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> let v17
                                                              = coe
                                                                  du_checkElabV'45'wf_6166 (coe v0)
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
                                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_Unit_120)
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
                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396
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
                              MAlonzo.Code.Once.Type.C_μ'45'type_130 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_132 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_rigid_138 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_66
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              du_inferSpine_6286 (coe v0) (coe v1)
                              (coe d_inferElabV_6150 (coe v0) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_6266 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'dispatch_6266 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'dispatch_6266 v0 v1 v2 v3
du_inferElabV'45'RApp'45'dispatch_6266 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'dispatch_6266 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_800
        -> let v4 = d_inferElabV_6150 (coe v0) (coe v2) in
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
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_id_20) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v8 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_802
        -> coe
             du_inferFstOn_2358 (coe v0)
             (coe d_inferElabV_6150 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_804
        -> coe
             du_inferSndOn_2434 (coe v0)
             (coe d_inferElabV_6150 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_806
        -> let v4 = d_inferElabV_6150 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_terminal_72) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v7
                                 v8 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_808
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_30))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_810
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_32))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_812
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_34))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_814
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_816
        -> coe
             du_inferApplyOn_2620 (coe v0)
             (coe d_inferElabV_6150 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_818
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_820
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'ana_822
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'Out_824
        -> coe d_inferOut_6056 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_828
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_832
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_836
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_840
        -> coe
             d_inferElabV'45'RApp'45'other_6174 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_6278 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'dispatch_6278 v0 v1 v2 v3 v4 ~v5
  = du_checkElabV'45'RApp'45'dispatch_6278 v0 v1 v2 v3 v4
du_checkElabV'45'RApp'45'dispatch_6278 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'dispatch_6278 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_800
        -> let v5 = d_inferElabV_6150 (coe v0) (coe v2) in
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
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_id_20) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280
                                         v9 v7) in
                            coe (coe du_embedOrSubsume_652 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_802
        -> let v5
                 = coe
                     du_inferFstOn_2358 (coe v0)
                     (coe d_inferElabV_6150 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_652 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_804
        -> let v5
                 = coe
                     du_inferSndOn_2434 (coe v0)
                     (coe d_inferElabV_6150 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_652 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_806
        -> let v5 = d_inferElabV_6150 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_88 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_terminal_72) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314
                                         v8 v9 v7) in
                            coe (coe du_embedOrSubsume_652 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_808
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_6166 (coe v0) (coe v2) (coe v5) in
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
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v10
                                           v5 (coe MAlonzo.Code.Once.IR.C_inl_54) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_686
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_810
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_122
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__124 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__126 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_6166 (coe v0) (coe v2) (coe v6) in
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
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v10
                                           v6 (coe MAlonzo.Code.Once.IR.C_inr_60) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_698
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_rigid_138 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_38))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_812
        -> let v5
                 = coe
                     du_checkElabV'45'wf_6166 (coe v0) (coe v2)
                     (coe MAlonzo.Code.Once.Type.C_Void_122) in
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
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8
                                    (coe MAlonzo.Code.Once.Type.C_Void_122)
                                    (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_708
                                 v8 v7)
                       C_failure_114 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_814
        -> coe d_checkCurry_6042 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_816
        -> let v5
                 = coe
                     du_inferApplyOn_2620 (coe v0)
                     (coe d_inferElabV_6150 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_652 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_818
        -> coe d_checkIn_6064 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_820
        -> coe d_checkCata_6090 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'ana_822
        -> coe d_checkAna_6120 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'Out_824
        -> let v5
                 = coe
                     du_inferOutOn_2282 (coe v0)
                     (coe d_inferElabV_6150 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_652 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_828
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkPair_5906 (coe v0)
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
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_832
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCompose_5974 (coe v0)
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
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_836
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCase_5938 (coe v0)
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
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_840
        -> let v6
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_6266 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                        (coe v1)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_88 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_652 (coe v3) (coe v6)
                       C_failure_90 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_6286 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSpine_6286 v0 v1 ~v2 ~v3 v4 = du_inferSpine_6286 v0 v1 v4
du_inferSpine_6286 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSpine_6286 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> let v10
                        = d_elabGivenV_5994
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
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412
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
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_6294 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RInt'45'aux_6294 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_success_88 (coe MAlonzo.Code.Once.Type.C_Int_134)
                 (coe
                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v1)
                 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0)))
              (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30) in
    coe (coe du_embedOrSubsume_652 (coe v2) (coe v3))
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_6304 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_RPairTarget_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RPair'45'aux_6304 v0 v1 v2 v3 v4
  = case coe v4 of
      C_rpt'45'prod_36
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> coe
                    d_checkPairLit_5928 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_46
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_114
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v9)
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
                     du_inferElabV'45'RPair'45'aux_2650
                     (coe d_inferElabV_6150 (coe v0) (coe v1))
                     (coe d_inferElabV_6150 (coe v0) (coe v2)) in
           coe (coe du_embedOrSubsume_652 (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_9762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab_9762 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inferElabV_6150 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_9776 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_98
d_checkElab_9776 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_checkElabV_6158 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_9794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkApply_9794 v0 v1 v2
  = let v3 = d_inferElabV_6150 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                C_success_88 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Unit_120
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Void_122
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'42'__124 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C_Unit_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_122
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__124 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
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
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                            (coe ("apply" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                     -> let v18
                                                              = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                                                                  (coe v13) (coe v12) in
                                                        coe
                                                          (let v19
                                                                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
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
                                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              v7)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430
                                                                                                        v7
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'42'__124
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
                                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_674
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
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_62
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
                                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_130 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_132 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_rigid_138 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'43'__126 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v11 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_μ'45'type_130 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_ν'45'type_132 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Int_134
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Float_136
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_rigid_138 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_78
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
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_10046 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab'45'RApp'45'other_10046 v0 v1 v2
  = let v3
          = coe
              du_asFun_1080
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe d_inferElabV_6150 (coe v0) (coe v1))) in
    coe
      (case coe v3 of
         C_isFun_1064 v4 v5 v6 v7 v8 v9 v10
           -> let v11
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe du_checkElabV'45'wf_6166 (coe v0) (coe v2) (coe v4)) in
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
         C_isEff_1072 v4 v5 v6 v7 v8 v9
           -> let v10
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe du_checkElabV'45'wf_6166 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v10 of
                   C_success_112 v11 v12 v13 v14
                     -> coe
                          C_success_88
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
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
         C_notFun_1074 v4 -> coe C_failure_90 (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
