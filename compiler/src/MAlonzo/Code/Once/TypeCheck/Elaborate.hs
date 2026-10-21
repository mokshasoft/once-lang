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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Name
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.Join
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Determined
import qualified MAlonzo.Code.Once.Type.Grade
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.TargetView
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.isRIntVliftTarget?
d_isRIntVliftTarget'63'_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRIntVliftTarget'63'_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Internal.Type.C_Int_34
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
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRFloatVliftTarget'63'_24 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Internal.Type.C_Float_36
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
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_RPairTarget_30
d_classifyRPairTarget_54 v0
  = let v1 = coe C_rpt'45'other_50 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Type.C__'42'__24 v2 v3
           -> coe C_rpt'45'prod_36
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
                                -> coe C_rpt'45'vlift_46
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_74 a0 a1 = ()
data T_InferElabResult_74
  = C_success_88 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_90 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_98 a0 a1 a2 = ()
data T_CheckElabResult_98
  = C_success_112 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_114 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.NegOperandView
d_NegOperandView_116 a0 = ()
data T_NegOperandView_116
  = C_nov'45'int_120 | C_nov'45'float_130 | C_nov'45'other_134
-- Once.TypeCheck.Elaborate.negOperandView
d_negOperandView_138 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_NegOperandView_116
d_negOperandView_138 v0
  = let v1 = coe C_nov'45'other_134 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v2
           -> coe C_nov'45'int_120
         MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v2 v3 v4 v5
           -> coe C_nov'45'float_130
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.soundOf
d_soundOf_156 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_InferElabResult_74 -> ()
d_soundOf_156 = erased
-- Once.TypeCheck.Elaborate.VerifiedInferResult
d_VerifiedInferResult_180 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 -> ()
d_VerifiedInferResult_180 = erased
-- Once.TypeCheck.Elaborate.checkSoundOf
d_checkSoundOf_194 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T_CheckElabResult_98 -> ()
d_checkSoundOf_194 = erased
-- Once.TypeCheck.Elaborate.VerifiedCheckResult
d_VerifiedCheckResult_222 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_VerifiedCheckResult_222 = erased
-- Once.TypeCheck.Elaborate.GivenElabResult
d_GivenElabResult_240 a0 a1 a2 a3 = ()
data T_GivenElabResult_240
  = C_success_258 MAlonzo.Code.Once.Internal.Type.T_Type_8
                  MAlonzo.Code.Once.Internal.Context.T_Usage_46
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_260 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.givenSoundOf
d_givenSoundOf_270 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_240 -> ()
d_givenSoundOf_270 = erased
-- Once.TypeCheck.Elaborate.VerifiedGivenResult
d_VerifiedGivenResult_306 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> ()
d_VerifiedGivenResult_306 = erased
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_338 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer'45'dec_338 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = du_given'45'infer'45'dec_338
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_given'45'infer'45'dec_338 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
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
                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                      (coe
                                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                         (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                            (coe v4))
                                                         (coe v2))
                                                      (coe
                                                         MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                                         v14
                                                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                                            (coe v2))
                                                         v17)
                                                      v6)
                                                   (coe v7) (coe v8))
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.C_d'45'infer_790
                                                   v1 v4 v9 v14 v17)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v16)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_260
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                     (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v3))
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                     (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                                (coe v2))
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-infer
d_given'45'infer_418 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'infer_418 ~v0 ~v1 v2 v3 v4
  = du_given'45'infer_418 v2 v3 v4
du_given'45'infer_418 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
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
                                  MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_78))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                       -> coe
                                            du_given'45'infer'45'dec_338 (coe v0) (coe v11)
                                            (coe v13) (coe v1) (coe v15) (coe v6) (coe v7) (coe v8)
                                            (coe v9) (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
                                               (coe v0) (coe v11))
                                            (coe
                                               MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
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
-- Once.TypeCheck.Elaborate.withUnit
d_withUnit_478 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit_478 ~v0 v1 v2 v3 = du_withUnit_478 v1 v2 v3
du_withUnit_478 ::
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit_478 v0 v1 v2
  = coe
      du_withUnit'45'aux_484 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (coe v1))
      (coe v2)
-- Once.TypeCheck.Elaborate.withUnit-aux
d_withUnit'45'aux_484 ::
  () ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'aux_484 ~v0 ~v1 v2 v3 v4
  = du_withUnit'45'aux_484 v2 v3 v4
du_withUnit'45'aux_484 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'aux_484 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v2 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v4) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-dec
d_given'45'cata'45'dec_524 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata'45'dec_524 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 v9 v10
                           v11 v12 v13
  = du_given'45'cata'45'dec_524 v3 v4 v6 v8 v9 v10 v11 v12 v13
du_given'45'cata'45'dec_524 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata'45'dec_524 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       du_withUnit_478
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_260
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                (coe ("cata" :: Data.Text.Text))))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe v0)
                       (coe
                          (\ v11 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_success_258 (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v3 v1 v4)
                                  (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                               (coe
                                  MAlonzo.Code.Once.Internal.Typing.C_d'45'cata_966 v3 v11 v1 v7))))
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_260
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                             (coe ("cata" :: Data.Text.Text))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_590 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'cata_590 ~v0 ~v1 v2 v3 v4 v5
  = du_given'45'cata_590 v2 v3 v4 v5
du_given'45'cata_590 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'cata_590 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> let v11
                        = coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_failure_260
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                  (coe ("cata" :: Data.Text.Text))))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v12 v13 v14
                         -> coe
                              du_given'45'cata'45'dec_524 (coe v1) (coe v2) (coe v14) (coe v7)
                              (coe v8) (coe v9) (coe v10) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                    (coe
                                       MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                       (coe v0) (coe v14))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
                                    (coe v14)))
                       _ -> coe v11)
             C_failure_90 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_260 (coe v6))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_654 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'dec_654 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'dec_654 v2 v3 v4 v5 v6 v7 v8 v9
du_embedOrSubsume'45'dec_654 ::
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'dec_654 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_112 (coe v0)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v2 v10 v3)
                              (coe v4) (coe v5))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_664 v2 v6 v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_114
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v1)
                             (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_696 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume_696 ~v0 ~v1 v2 v3 = du_embedOrSubsume_696 v2 v3
du_embedOrSubsume_696 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume_696 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_embedOrSubsume'45'dec_654 (coe v5) (coe v0) (coe v4) (coe v6)
                    (coe v7) (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v4) (coe v0))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_726 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specId_726 ~v0 = du_specId_726
du_specId_726 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specId_726
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_734 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specFst_734 ~v0 ~v1 = du_specFst_734
du_specFst_734 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specFst_734
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_744 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specSnd_744 ~v0 ~v1 = du_specSnd_744
du_specSnd_744 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specSnd_744
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_754 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInl_754 ~v0 ~v1 = du_specInl_754
du_specInl_754 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInl_754
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_764 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInr_764 ~v0 ~v1 = du_specInr_764
du_specInr_764 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInr_764
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_770 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specUnitGen_770 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158
-- Once.TypeCheck.Elaborate.specPair
d_specPair_778 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specPair_778 v0 ~v1 ~v2 = du_specPair_778 v0
du_specPair_778 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specPair_778 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_pair_82
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_788 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specTerminal_788 ~v0 = du_specTerminal_788
du_specTerminal_788 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specTerminal_788
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_794 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInitial_794 ~v0 = du_specInitial_794
du_specInitial_794 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInitial_794
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_804 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCurry_804 v0 v1 ~v2 = du_specCurry_804 v0 v1
du_specCurry_804 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCurry_804 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_50
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_82
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_816 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specApply_816 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_50
         (coe
            MAlonzo.Code.Once.Internal.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
            (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))
         (coe
            MAlonzo.Code.Once.Internal.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
            (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))
         v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_106
            (MAlonzo.Code.Once.Internal.Type.d__'8658'__50 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_828 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCompose_828 v0 v1 ~v2 = du_specCompose_828 v0 v1
du_specCompose_828 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCompose_828 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_50
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               v1 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specCase
d_specCase_842 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCase_842 v0 v1 ~v2 = du_specCase_842 v0 v1
du_specCase_842 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCase_842 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
         (coe
            MAlonzo.Code.Once.Type.Grade.d__'8852'q__12
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
            (coe
               MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_34
         (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
            (coe
               MAlonzo.Code.Once.Type.Grade.d__'8852'q__12
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
               (coe
                  MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_34
            (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
               (coe
                  MAlonzo.Code.Once.Type.Grade.d__'8852'q__12
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_case''_152
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (coe
                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48))))
               (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
               (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
               v0 v1
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_50
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                              (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48)))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48)))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48)))))
                  (coe
                     MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Internal.Context.C_'91''93'_48)))))
                  v1 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
d_extract'45'morph'45'aux_866 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph'45'aux_866 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_extract'45'morph'45'aux_866 v3 v7
du_extract'45'morph'45'aux_866 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_866 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_884 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_884 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_extract'45'morph_884 v3 v4 v5 v6
du_extract'45'morph_884 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_884 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_866
      (coe
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_890 a0 = ()
data T_WellFormedFView_890
  = C_wfv'45'yes_896 MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 |
    C_wfv'45'no_898
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_902 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  T_WellFormedFView_890
d_inspectWellFormedF_902 v0
  = let v1
          = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe C_wfv'45'yes_896 v2
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_898
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_918 = ()
data T_AppSpine_918
  = C_mkSpine_928 MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34
                  [MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_924 ::
  T_AppSpine_918 -> MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34
d_head_924 v0
  = case coe v0 of
      C_mkSpine_928 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_926 ::
  T_AppSpine_918 -> [MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34]
d_args_926 v0
  = case coe v0 of
      C_mkSpine_928 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_930 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 -> T_AppSpine_918
d_spineOf_930 v0
  = coe
      du_go_938 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_938 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34] -> T_AppSpine_918
d_go_938 ~v0 v1 v2 = du_go_938 v1 v2
du_go_938 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34] -> T_AppSpine_918
du_go_938 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Syntax.C_RVar_36 v2
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RQualified_38 v2 v3
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v2
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v2 v3
        -> coe
             du_go_938 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v2 v3
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RLet_46 v2 v3 v4
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v2 v3
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RUnit_52
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v2
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v2 v3 v4 v5
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_58 v2 v3
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v2 v3 v4
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v3
        -> coe
             C_mkSpine_928
             (coe MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v3) (coe v1)
      MAlonzo.Code.Once.Internal.Syntax.C_RAna_64 v2 v3
        -> coe C_mkSpine_928 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_1034 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_1034 v0
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
d_matchInferResult_1042 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CheckElabResult_98
d_matchInferResult_1042 ~v0 ~v1 v2 v3
  = du_matchInferResult_1042 v2 v3
du_matchInferResult_1042 ::
  T_InferElabResult_74 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CheckElabResult_98
du_matchInferResult_1042 v0 v1
  = case coe v0 of
      C_success_88 v2 v3 v4 v5 v6
        -> let v7
                 = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                     (coe v1) (coe v2) in
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
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_90 v2 -> coe C_failure_114 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1090 a0 a1 = ()
data T_FunProjection_1090
  = C_isFun_1104 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_isEff_1116 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                 MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notFun_1118 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1124 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_FunProjection_1090
d_asFun_1124 ~v0 ~v1 v2 = du_asFun_1124 v2
du_asFun_1124 :: T_InferElabResult_74 -> T_FunProjection_1090
du_asFun_1124 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                    -> coe
                                         C_isFun_1104 (coe v6) (coe v9) (coe v8) (coe v2) (coe v3)
                                         (coe v4) (coe v5)
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> case coe v9 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_notFun_1118
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                   (coe v1))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_notFun_1118
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                   (coe v1))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_isEff_1116 (coe v10)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                (coe v6) (coe v8) (coe v2) (coe v3) (coe v4)
                                                (coe v5)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         C_notFun_1118
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                            (coe v1))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         C_notFun_1118
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                            (coe v1))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         C_isEff_1116 (coe v10)
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) (coe v6)
                                         (coe v8) (coe v2) (coe v3) (coe v4) (coe v5)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    C_notFun_1118
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notFun_1118 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1214 a0 a1 = ()
data T_IntProjection_1214
  = C_isInt_1222 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notInt_1224 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1230 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  T_InferElabResult_74 -> T_IntProjection_1214
d_asInt_1230 ~v0 ~v1 v2 = du_asInt_1230 v2
du_asInt_1230 :: T_InferElabResult_74 -> T_IntProjection_1214
du_asInt_1230 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe C_isInt_1222 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    C_notInt_1224
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1 -> coe C_notInt_1224 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1270 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1270 ~v0 ~v1 v2 = du_notNumeric_1270 v2
du_notNumeric_1270 ::
  T_InferElabResult_74 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1270 v0
  = case coe v0 of
      C_success_88 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_90 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1302 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1302 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased)
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab-RApp-id
d_inferElab'45'RApp'45'id_1306 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  T_InferElabResult_74 -> T_InferElabResult_74
d_inferElab'45'RApp'45'id_1306 v0 v1
  = case coe v1 of
      C_success_88 v2 v3 v4 v5 v6
        -> coe
             C_success_88 (coe v2)
             (coe
                MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_90 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_1326 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_1326 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_1368 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'k_1368 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19
  = du_given'45'poly'45'k_1368
      v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v11 v16 v17 v18 v19
du_given'45'poly'45'k_1368 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'k_1368 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
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
                                 MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                       (coe v2))
                                    (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                                       (coe v3))
                                    v13)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1))
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_d'45'poly_814 v4 v6 v7 v8 v9
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
d_given'45'poly'45'π_1452 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'π_1452 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16 v17 ~v18 v19
  = du_given'45'poly'45'π_1452
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v15 v16 v17 v19
du_given'45'poly'45'π_1452 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'π_1452 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v13 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
        -> if coe v14
             then case coe v15 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                      -> coe
                           du_given'45'poly'45'k_1368 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Type.Poly.d_substPoly_162 (coe v12)
                              (coe v6))
                           (coe v7) (coe v3) (coe v4) (coe v5) (coe v6) (coe v8) (coe v9)
                           (coe v10) (coe v11) (coe v16)
                           (coe
                              MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_556 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.Poly.d_substPoly_162 (coe v12)
                                    (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v15)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_260 (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-m
d_given'45'poly'45'm_1538 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'm_1538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16 v17 ~v18
  = du_given'45'poly'45'm_1538
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v15 v16 v17
du_given'45'poly'45'm_1538 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'm_1538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13
  = case coe v13 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
        -> coe
             du_given'45'poly'45'π_1452 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Type.Instance.du_instantiate'45'sound_1804
                   (coe v6) (coe v2) (coe v14)))
             (coe
                MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10 (coe v8) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_260 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-d
d_given'45'poly'45'd_1614 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'd_1614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          ~v12 ~v13 ~v14 v15 v16
  = du_given'45'poly'45'd_1614
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v15 v16
du_given'45'poly'45'd_1614 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'd_1614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12
  = case coe v12 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then case coe v14 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                      -> coe
                           du_given'45'poly'45'm_1538 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                           (coe v11) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Type.Match.d_instantiate_90 (coe v6) (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_260 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1676 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'a_1676 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11
                          v12
  = du_given'45'poly'45'a_1676 v0 v1 v2 v3 v4 v5 v6 v7 v12
du_given'45'poly'45'a_1676 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'a_1676 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v13 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  du_given'45'poly'45'd_1614 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v10) (coe v12) (coe v14) (coe v6) (coe v7)
                                  (coe v15)
                                  (coe
                                     MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_578
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
d_given'45'poly'45'g_1740 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly'45'g_1740 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
                          ~v12
  = du_given'45'poly'45'g_1740 v0 v1 v2 v3 v4 v5 v6 v7 v11
du_given'45'poly'45'g_1740 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly'45'g_1740 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                du_given'45'poly'45'a_1676 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_596 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1796 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'poly_1796 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10
  = du_given'45'poly_1796 v0 v1 v2 v3 v4 v5 v7 v9
du_given'45'poly_1796 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'poly_1796 v0 v1 v2 v3 v4 v5 v6 v7
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
                                         du_given'45'poly'45'g_1740 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe v4) (coe v9) (coe v11) (coe v12)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_96 (coe v9))
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
-- Once.TypeCheck.Elaborate.given-res
d_given'45'res_1858 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'res_1858 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             C_success_88 v7 v8 v9 v10 v11
               -> coe du_given'45'infer_418 (coe v2) (coe v3) (coe v4)
             C_failure_90 v7
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v8
                      -> case coe v8 of
                           []
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_260 (coe v7))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (:) v9 v10
                             -> case coe v10 of
                                  []
                                    -> coe
                                         du_given'45'poly_1796 (coe v0) (coe v9) (coe v2) (coe v3)
                                         (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_128
                                               (coe v0))
                                            (coe v9))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_124
                                               (coe v0))
                                            (coe v9))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_68
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_126
                                               (coe v0))
                                            (coe v9))
                                  (:) v11 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe C_failure_260 (coe v7))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-inst-aux
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910 v0 v1 ~v2 v3 v4 v5
                                                 v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910
      v0 v1 v3 v4 v5 v6 v11
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910 v0 v1 v2 v3 v4 v5
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
                                 MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate_772
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
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962 v0 v1 v2 v3 v4
                                                   v5 v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962
      v0 v1 v2 v3 v4 v5 v6 v10
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962 v0 v1 v2 v3 v4
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
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1910 (coe v0) (coe v1)
                (coe v3) (coe v4) (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_556 (coe v4)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_2012 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'poly'45'check'45'aux_2012 v0 v1 v2 v3 v4
                                                  ~v5 v6 ~v7 v8 ~v9
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_2012
      v0 v1 v2 v3 v4 v6 v8
du_checkElabV'45'RVar'45'poly'45'check'45'aux_2012 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'poly'45'check'45'aux_2012 v0 v1 v2 v3 v4
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
                                         du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1962
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v10)
                                         (coe v11)
                                         (coe MAlonzo.Code.Once.Type.d_isGround_96 (coe v8))
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
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068 v0 v1 ~v2 ~v3 v4
                                                   v5 ~v6 v7 ~v8
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068
      v0 v1 v4 v5 v7
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88
                (coe
                   MAlonzo.Code.Once.Internal.Type.Poly.d_extractGround_88 (coe v2)
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102
                v2 v3
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.du_lookupPoly'8658'lookupPolyPrefix_274
                      (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_126 (coe v0))
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
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 v0 v1 ~v2 ~v3 v4
                                                   ~v5
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 v0 v1 v4
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2068 (coe v0)
                    (coe v1) (coe v4) (coe v5)
                    (coe MAlonzo.Code.Once.Type.d_isGround_96 (coe v4))
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
d_inferElabV'45'RVar'45'poly'45'aux_2134 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'aux_2134 v0 v1 ~v2 ~v3
  = du_inferElabV'45'RVar'45'poly'45'aux_2134 v0 v1
du_inferElabV'45'RVar'45'poly'45'aux_2134 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'aux_2134 v0 v1
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2106 (coe v0)
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_10
         (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_126 (coe v0))
         (coe v1))
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_2152 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenLeaf_2152 v0 v1 v2 v3 v4 v5
  = let v6
          = d_given'45'res_1858
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_296
           -> coe
                du_withUnit_478
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      C_failure_260
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                         (coe ("id" :: Data.Text.Text))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe v3)
                (coe
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_success_258 (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                              (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                              (coe MAlonzo.Code.Once.IR.C_id_20))
                           (coe (0 :: Integer)) (coe (0 :: Integer)))
                        (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'id_864 v7)))
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_298
           -> let v7
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                              (coe ("fst" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                     -> coe
                          du_withUnit_478
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_260
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                   (coe ("fst" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v3)
                          (coe
                             (\ v10 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_258 (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                        (coe MAlonzo.Code.Once.IR.C_fst_42))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'fst_876 v10)))
                   _ -> coe v7)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_300
           -> let v7
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                              (coe ("snd" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                     -> coe
                          du_withUnit_478
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_260
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                   (coe ("snd" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v3)
                          (coe
                             (\ v10 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_258 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                        (coe MAlonzo.Code.Once.IR.C_snd_48))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'snd_888 v10)))
                   _ -> coe v7)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_302
           -> coe
                du_withUnit_478
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      C_failure_260
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                         (coe ("terminal" :: Data.Text.Text))))
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                (coe v3)
                (coe
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_success_258 (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                           (coe
                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                              (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                              (coe MAlonzo.Code.Once.IR.C_terminal_72))
                           (coe (0 :: Integer)) (coe (0 :: Integer)))
                        (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'terminal_898 v7)))
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_308
           -> let v7
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                              (coe ("initial" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Internal.Type.C_Void_22
                     -> coe
                          du_withUnit_478
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                C_failure_260
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                   (coe ("initial" :: Data.Text.Text))))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe v3)
                          (coe
                             (\ v8 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_258 (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                        (coe MAlonzo.Code.Once.IR.C_initial_76))
                                     (coe (0 :: Integer)) (coe (0 :: Integer)))
                                  (coe MAlonzo.Code.Once.Internal.Typing.C_d'45'initial_906 v8)))
                   _ -> coe v7)
         _ -> coe v6)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_2222 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_2222 v0 ~v1 v2 = du_outIR_2222 v0 v2
du_outIR_2222 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_2222 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
         (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_2252 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutGo_2252 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inferOutGo_2252 v0 v2 v3 v4 v5 v6 v7 v8 v9
du_inferOutGo_2252 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutGo_2252 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v1) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                          (coe
                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v3
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v1) (coe v2))
                          (coe du_outIR_2222 (coe v1) (coe v9)) v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'app'45'infer_356 v1
                       v3 v9 v7)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                          (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v2)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v1) (coe v2))))
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                          (coe
                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v3
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v1) (coe v2))
                          (coe
                             MAlonzo.Code.Once.IR.C_curry_84
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                   (coe
                                      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v1)
                                      (coe v2)))
                                (coe du_outIR_2222 (coe v1) (coe v9))
                                (coe MAlonzo.Code.Once.IR.C_fst_42)))
                          v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'Out'45'eff'45'app'45'infer_368
                       v1 v3 v9 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutAt
d_inferOutAt_2326 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutAt_2326 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferOutAt_2326 v0 v2 v3 v4 v5 v6 v7 v8
du_inferOutAt_2326 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutAt_2326 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'at_218
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v10 v11
               -> coe
                    du_inferOutGo_2252 (coe v0) (coe v10) (coe v11) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'other_222
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("Out" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutOn
d_inferOutOn_2364 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOutOn_2364 v0 ~v1 v2 = du_inferOutOn_2364 v0 v2
du_inferOutOn_2364 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferOutOn_2364 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferOutAt_2326 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe MAlonzo.Code.Once.TypeCheck.TargetView.d_nuView_226 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstAt
d_inferFstAt_2402 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstAt_2402 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferFstAt_2402 v0 v2 v3 v4 v5 v6 v7 v8
du_inferFstAt_2402 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstAt_2402 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_266
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                          (coe
                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_fst_42) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'app_294 v11 v2 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_270
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstOn
d_inferFstOn_2440 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferFstOn_2440 v0 ~v1 v2 = du_inferFstOn_2440 v0 v2
du_inferFstOn_2440 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferFstOn_2440 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferFstAt_2402 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_prodView_274 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndAt
d_inferSndAt_2478 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndAt_2478 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferSndAt_2478 v0 v2 v3 v4 v5 v6 v7 v8
du_inferSndAt_2478 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndAt_2478 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_266
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                          (coe
                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v2 v1
                          (coe MAlonzo.Code.Once.IR.C_snd_48) v3)
                       (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'app_306 v10 v2 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_270
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndOn
d_inferSndOn_2516 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSndOn_2516 v0 ~v1 v2 = du_inferSndOn_2516 v0 v2
du_inferSndOn_2516 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSndOn_2516 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferSndAt_2478 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_prodView_274 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyAt
d_inferApplyAt_2554 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_232 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyAt_2554 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferApplyAt_2554 v0 v2 v3 v4 v5 v6 v7 v8
du_inferApplyAt_2554 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_232 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyAt_2554 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'at_242
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v14 v15 v16
                      -> case coe v15 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v19
                                    -> case coe v19 of
                                         MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                           -> let v20
                                                    = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                                        (coe v14) (coe v13) in
                                              coe
                                                (case coe v20 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> if coe v21
                                                          then coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_88 (coe v16)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                                (coe v0)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                             (coe v2)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434
                                                                          v2
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v14)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                                   (coe v18))
                                                                                (coe v16))
                                                                             (coe v14))
                                                                          (coe
                                                                             MAlonzo.Code.Once.IR.C_apply_90)
                                                                          v3)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v4))
                                                                       (coe v5))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'app'45'infer_328
                                                                       v14 v2 v6))
                                                          else coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_failure_90
                                                                       (coe
                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                          (coe
                                                                             ("apply"
                                                                              ::
                                                                              Data.Text.Text))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                           -> let v20
                                                    = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                                        (coe v14) (coe v13) in
                                              coe
                                                (case coe v20 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> if coe v21
                                                          then coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_88
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                             (coe v18))
                                                                          (coe v16))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                                (coe v0)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                             (coe v2)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434
                                                                          v2
                                                                          (coe
                                                                             MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                                             (coe
                                                                                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                (coe v14)
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v4))
                                                                       (coe v5))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_344
                                                                       v14 v2
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                       v6))
                                                          else coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_failure_90
                                                                       (coe
                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                          (coe
                                                                             ("apply"
                                                                              ::
                                                                              Data.Text.Text))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> let v19
                                             = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
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
                                                                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                      (coe
                                                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                      (coe v18))
                                                                   (coe v16))
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                      (coe
                                                                         MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                         (coe v0)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                      (coe
                                                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                      (coe v2)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434
                                                                   v2
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                                      (coe
                                                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                         (coe v14)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                            (coe
                                                                               MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                                                                MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'eff'45'app'45'infer_344
                                                                v14 v2
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                v6))
                                                   else coe
                                                          seq (coe v21)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_90
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'other_246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("apply" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyOn
d_inferApplyOn_2766 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferApplyOn_2766 v0 ~v1 v2 = du_inferApplyOn_2766 v0 v2
du_inferApplyOn_2766 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferApplyOn_2766 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_88 v4 v5 v6 v7 v8
               -> coe
                    du_inferApplyAt_2554 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                    (coe v8) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.d_applyView_250 (coe v4))
             C_failure_90 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_2796 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RPair'45'aux_2796 ~v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RPair'45'aux_2796 v3 v4
du_inferElabV'45'RPair'45'aux_2796 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RPair'45'aux_2796 v0 v1
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
                                     (coe
                                        MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v4)
                                        (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                        (coe v5) (coe v12))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v5 v12 v6 v13)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                        (coe v14))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'pair_128 v5 v12 v3
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
d_inferElabV'45'RAnnot'45'aux_2850 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RAnnot'45'aux_2850 ~v0 ~v1 v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_2850 v2 v3 v4
du_inferElabV'45'RAnnot'45'aux_2850 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RAnnot'45'aux_2850 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v4 of
                    C_success_112 v6 v7 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_success_88 (coe v0) (coe v6) (coe v7) (coe v8) (coe v9))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'annot_112 v3 v5)
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_AnnotationMentionsParameter_86
                   (coe v0)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RUnaryOp-aux
d_inferElabV'45'RUnaryOp'45'aux_2890 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RUnaryOp'45'aux_2890 ~v0 ~v1 v2
  = du_inferElabV'45'RUnaryOp'45'aux_2890 v2
du_inferElabV'45'RUnaryOp'45'aux_2890 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RUnaryOp'45'aux_2890 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_88 v3 v4 v5 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Type.C_Unit_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Void_22
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Int_34
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v3) (coe v4)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v5)
                              (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_136 v2)
                    MAlonzo.Code.Once.Internal.Type.C_Float_36
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_rigid_38 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_2978 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'int'45'aux_2978 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
              (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v2) in
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
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) v6
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_int_190
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))))
                                 (coe (1 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_664
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_136
                                    (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_30))
                                 v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v2)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_3016 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'float'45'aux_3016 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'neg'45'float'45'aux_3016 v0 v1 v2 v3 v5
du_checkElabV'45'neg'45'float'45'aux_3016 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'neg'45'float'45'aux_3016 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
              (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v4) in
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
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_198
                                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                                          (coe
                                             MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                             (coe v1) (coe v2) (coe v3)))))
                                 (coe (1 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_664
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                 (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_148) v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v4)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_3068 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'aux_3068 ~v0 v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RBinOp'45'aux_3068 v1 v4 v5
du_inferElabV'45'RBinOp'45'aux_3068 ::
  MAlonzo.Code.Once.Internal.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'aux_3068 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C_Unit_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Void_22
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Int_34
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Internal.Type.C_Unit_20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_Void_22
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'42'__24 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_Int_34
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_add_208
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_216
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_sub_218
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_216
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mul_228
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_216
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_div_286
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_216
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mod''_296
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith_216
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lt_314
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_le_324
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_gt_334
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ge_344
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_eq_354
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Type.C__'43'__26
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Type.C_Unit_20))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ne_364
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'cmp_272
                                                          v6 v13 v4 v11)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Internal.Type.C_Float_36
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_244
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_244
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_244
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'il_244
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Internal.Type.C_rigid_38 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Internal.Type.C_Float_36
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_88 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Internal.Type.C_Unit_20
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_Void_22
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'42'__24 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Internal.Type.C_Int_34
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_258
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_258
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_258
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float'45'ir_258
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Internal.Type.C_Float_36
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_230
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_230
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_230
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_88 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'binop'45'arith'45'float_230
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.Internal.Syntax.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_90
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Internal.Type.C_rigid_38 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_90
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_90 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_90
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_82
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Internal.Type.C_rigid_38 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Int_34) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_80 (coe v5)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_4108 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux2_4108 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                  v9 v10
  = du_inferElabV'45'RLet'45'aux2_4108 v4 v5 v6 v7 v9 v10
du_inferElabV'45'RLet'45'aux2_4108 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux2_4108 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> case coe v9 of
                    MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_88 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v14)
                                    (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v1 v15 v14 v0 v2 v10)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)))
                              (coe v12))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.C_t'45'let_168 v0 v14 v1 v15 v4
                              v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-join
d_inferElabV'45'RDestruct'45'join_4208 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'join_4208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                       v23 v24 v25
  = du_inferElabV'45'RDestruct'45'join_4208
      v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
      v24 v25
du_inferElabV'45'RDestruct'45'join_4208 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'join_4208 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.Internal.Type.Join.C_joined_162 v20 v21
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe v20)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Internal.Context.du__'8852''7512'__100 (coe v8)
                      (coe v14)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v2 v8 v14 v7 v13 v0
                   v1 v3
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v6
                      (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''7580''8658''60''58'_176
                         (coe v6) (coe v20)
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.d_left_242
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Join.d_sound_658 (coe v6) (coe v12)
                               (coe v20) (coe v21))))
                      v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v12
                      (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''7580''8658''60''58'_176
                         (coe v12) (coe v20)
                         (coe
                            MAlonzo.Code.Once.Internal.Type.Sub.d_right_244
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Join.d_sound_658 (coe v6) (coe v12)
                               (coe v20) (coe v21))))
                      v15))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4)
                      (coe addInt (coe (1 :: Integer)) (coe v10)))
                   (coe addInt (coe (1 :: Integer)) (coe v16)))
                (coe v17))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_t'45'case_202 v0 v1 v6 v12 v7
                v13 v2 v8 v14 v5 v11 v18
                (MAlonzo.Code.Once.Internal.Type.Join.d_sound_658
                   (coe v6) (coe v12) (coe v20) (coe v21)))
      MAlonzo.Code.Once.Internal.Type.Join.C_apart_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_48))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-case-join
d_given'45'case'45'join_4320 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_given'45'case'45'join_4320 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16 v17
  = du_given'45'case'45'join_4320
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_given'45'case'45'join_4320 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Internal.Type.Join.T_Join'63'_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_given'45'case'45'join_4320 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14
  = case coe v14 of
      MAlonzo.Code.Once.Internal.Type.Join.C_joined_162 v15 v16
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_258 (coe v15)
                (coe
                   MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v4)
                   (coe v9))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v4 v9
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v0)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                            (coe v0))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''7580''8658''60''58'_176
                            (coe v3) (coe v15)
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.d_left_242
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Join.d_sound_658 (coe v3) (coe v8)
                                  (coe v15) (coe v16))))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_80
                            (coe v2)))
                      v5)
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                      (coe
                         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v1)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
                         (coe v8))
                      (coe
                         MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''45'refl_84
                            (coe v1))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'60''58''7580''8658''60''58'_176
                            (coe v8) (coe v15)
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Sub.d_right_244
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.Join.d_sound_658 (coe v3) (coe v8)
                                  (coe v15) (coe v16))))
                         (MAlonzo.Code.Once.Internal.Type.Sub.d_'8849'π'45'refl_80
                            (coe v2)))
                      v10))
                (coe
                   addInt (coe (1 :: Integer))
                   (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v6) (coe v11)))
                (coe v12))
             (coe
                MAlonzo.Code.Once.Internal.Typing.C_d'45'case_930 v3 v8 v4 v9 v7
                v13
                (MAlonzo.Code.Once.Internal.Type.Join.d_sound_658
                   (coe v3) (coe v8) (coe v15) (coe v16)))
      MAlonzo.Code.Once.Internal.Type.Join.C_apart_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_260
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v3)
                   (coe v8)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_4422 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxR_4422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7 v8 v9 v10 ~v11 v12 v13 v14 v15 v16 v17 ~v18 v19 v20
  = du_inferElabV'45'RDestruct'45'auxR_4422
      v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v19 v20
du_inferElabV'45'RDestruct'45'auxR_4422 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxR_4422 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
        -> case coe v13 of
             C_success_88 v15 v16 v17 v18 v19
               -> case coe v16 of
                    MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v21 v22
                      -> coe
                           du_inferElabV'45'RDestruct'45'join_4208 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                           (coe v10) (coe v11) (coe v15) (coe v21) (coe v22) (coe v17)
                           (coe v18) (coe v19) (coe v14)
                           (coe
                              MAlonzo.Code.Once.Internal.Type.Join.d_join'63'_582 (coe v6)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-sem
d_ext'45'resolved'45'sem_4510 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
d_ext'45'resolved'45'sem_4510 ~v0 ~v1 v2 v3 v4
  = du_ext'45'resolved'45'sem_4510 v2 v3 v4
du_ext'45'resolved'45'sem_4510 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74
du_ext'45'resolved'45'sem_4510 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Once.SigOp.Info.C_ffiV_82
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v1 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                      -> if coe v4
                           then coe
                                  seq (coe v5) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_88)
                           else coe
                                  seq (coe v5)
                                  (case coe v2 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                       -> if coe v6
                                            then coe
                                                   seq (coe v7)
                                                   (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_86)
                                            else coe
                                                   seq (coe v7)
                                                   (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_84)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> case coe v1 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
               -> if coe v3
                    then coe
                           seq (coe v4) (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_88)
                    else coe
                           seq (coe v4)
                           (case coe v2 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> if coe v5
                                     then coe
                                            seq (coe v6)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_86)
                                     else coe
                                            seq (coe v6)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_callsV_84)
                              _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info-aux
d_ext'45'resolved'45'info'45'aux_4516 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ext'45'resolved'45'info'45'aux_4516 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_ext'45'resolved'45'info'45'aux_4516 v2 v3 v4 v5 v6 v7
du_ext'45'resolved'45'info'45'aux_4516 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_ext'45'resolved'45'info'45'aux_4516 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_118 (coe v0)
      (coe du_ext'45'resolved'45'sem_4510 (coe v1) (coe v2) (coe v3))
      (coe v4) (coe v5)
-- Once.TypeCheck.Elaborate.ext-resolved-info
d_ext'45'resolved'45'info_4534 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
d_ext'45'resolved'45'info_4534 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_ext'45'resolved'45'info_4534 v1 v3 v4 v5 v6
du_ext'45'resolved'45'info_4534 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96
du_ext'45'resolved'45'info_4534 v0 v1 v2 v3 v4
  = coe
      du_ext'45'resolved'45'info'45'aux_4516 (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84 (coe v0))
      (coe MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88 (coe v0))
      (coe v3) (coe v4)
-- Once.TypeCheck.Elaborate.resolvedArrowTerm
d_resolvedArrowTerm_4558 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvedArrowTerm_4558 v0 v1 ~v2 v3 v4 v5 v6
  = du_resolvedArrowTerm_4558 v0 v1 v3 v4 v5 v6
du_resolvedArrowTerm_4558 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvedArrowTerm_4558 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
      (coe
         MAlonzo.Code.Once.IR.C_SigOp_140 (coe v0) (coe v1)
         (coe
            du_ext'45'resolved'45'info_4534 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5)))
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-word
d_inferElabV'45'RResolved'45'word_4576 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'word_4576 ~v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'word_4576 v1 v2 v3
du_inferElabV'45'RResolved'45'word_4576 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'word_4576 v0 v1 v2
  = if coe v2
      then coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v0))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_4606 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'arrow'45'aux_4606 v0 v1 v2 v3 v4 v5
                                               ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RResolved'45'arrow'45'aux_4606
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RResolved'45'arrow'45'aux_4606 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'arrow'45'aux_4606 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_inferElabV'45'RResolved'45'word_4576 (coe v1)
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               C_success_88
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                  (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                  (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                               (coe
                                  du_resolvedArrowTerm_4558 (coe v3) (coe v4) (coe v1) (coe v5)
                                  (coe v8) (coe v9))
                               (coe (0 :: Integer)) (coe (0 :: Integer)))
                            (coe
                               MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_70 v2 v10
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.WellFormed.C_con'45'fun_46 v8
                                  v9))))
                    (coe MAlonzo.Code.Once.Internal.Name.d_wordNameB_36 (coe v1))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v1))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
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
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.resolvedValueTerm
d_resolvedValueTerm_4662 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvedValueTerm_4662 ~v0 ~v1 ~v2 v3 v4
  = du_resolvedValueTerm_4662 v3 v4
du_resolvedValueTerm_4662 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvedValueTerm_4662 v0 v1
  = coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v0 v1
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_4676 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'value'45'aux_4676 v0 v1 v2 v3 ~v4 v5
                                               ~v6
  = du_inferElabV'45'RResolved'45'value'45'aux_4676 v0 v1 v2 v3 v5
du_inferElabV'45'RResolved'45'value'45'aux_4676 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'value'45'aux_4676 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_inferElabV'45'RResolved'45'word_4576 (coe v1)
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        C_success_88 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                        (coe du_resolvedValueTerm_4662 (coe v1) (coe v5))
                        (coe (0 :: Integer)) (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'resolved_70 v2 v6
                        v5)))
             (coe MAlonzo.Code.Once.Internal.Name.d_wordNameB_36 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-def
d_inferElabV'45'RResolved'45'def_4706 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'def_4706 v0 v1 ~v2
  = du_inferElabV'45'RResolved'45'def_4706 v0 v1
du_inferElabV'45'RResolved'45'def_4706 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'def_4706 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        C_failure_90
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                           (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v1))))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
           coe
             (case coe v2 of
                (:) v4 v5
                  -> case coe v5 of
                       []
                         -> coe
                              du_inferElabV'45'RResolved'45'own'45'aux_4714 (coe v0) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                                 (coe
                                    MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_124 (coe v0))
                                 (coe v4))
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-own-aux
d_inferElabV'45'RResolved'45'own'45'aux_4714 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'own'45'aux_4714 v0 v1 ~v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'own'45'aux_4714 v0 v1 v3
du_inferElabV'45'RResolved'45'own'45'aux_4714 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'own'45'aux_4714 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe v3)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v1)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'own_78)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_inferElabV'45'RVar'45'poly'45'aux_2134 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_4722 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'aux_4722 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'aux_4722 v0 v1 v2 v3
du_inferElabV'45'RResolved'45'aux_4722 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'aux_4722 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_4676 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_4606 (coe v0)
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
        -> coe du_inferElabV'45'RResolved'45'def_4706 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-import-value-aux
d_inferElabV'45'RVar'45'import'45'value'45'aux_4794 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'import'45'value'45'aux_4794 v0 v1 ~v2 v3
                                                    ~v4 v5 ~v6 v7 ~v8
  = du_inferElabV'45'RVar'45'import'45'value'45'aux_4794
      v0 v1 v3 v5 v7
du_inferElabV'45'RVar'45'import'45'value'45'aux_4794 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'import'45'value'45'aux_4794 v0 v1 v2 v3 v4
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
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v1)
                                 (coe (0 :: Integer)) (coe (0 :: Integer)))
                              (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'import_86 v7)
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
d_inferElabV'45'RVar'45'lookup'45'aux_4842 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'lookup'45'aux_4842 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RVar'45'lookup'45'aux_4842 v0 v1 v2 v4
du_inferElabV'45'RVar'45'lookup'45'aux_4842 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'lookup'45'aux_4842 v0 v1 v2 v3
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
                                 MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_558 (coe v8))
                              (coe (0 :: Integer)) (coe (0 :: Integer)))
                           (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'var'45'local_62 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    du_inferElabV'45'RVar'45'import'45'value'45'aux_4794 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_22 (coe v1))
                    (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_90
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4880 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4880 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_114 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_114 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> let v8
                               = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                   (coe v3) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then coe
                                            seq (coe v10)
                                            (coe
                                               du_withUnit_478
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_114
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                        (coe ("id" :: Data.Text.Text))))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                               (coe v7)
                                               (coe
                                                  (\ v11 ->
                                                     coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_112
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                             (coe
                                                                MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                (coe v0)))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                             (coe MAlonzo.Code.Once.IR.C_id_20))
                                                          (coe (0 :: Integer)) (coe (0 :: Integer)))
                                                       (coe
                                                          MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'check_432
                                                          v11))))
                                     else coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_114
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4972 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4972 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v10
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                          (coe v6) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      du_withUnit_478
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_114
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                               (coe ("fst" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v9)
                                                      (coe
                                                         (\ v13 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_112
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_fst_42))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'fst'45'check_444
                                                                 v13))))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5110 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5110 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v10
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                          (coe v7) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      du_withUnit_478
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_114
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                               (coe ("snd" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v9)
                                                      (coe
                                                         (\ v13 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_112
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_snd_48))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'snd'45'check_456
                                                                 v13))))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5248 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5248 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Type.C_Unit_20
                             -> coe
                                  du_withUnit_478
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("terminal" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             C_success_112
                                             (coe
                                                MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                             (coe (0 :: Integer)) (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_466
                                             v8)))
                           MAlonzo.Code.Once.Internal.Type.C_Void_22
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'43'__26 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Int_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Float_36
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_rigid_38 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5354 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5354 v0 v1
                                                              v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> coe
                                  du_withUnit_478
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("initial" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             C_success_112
                                             (coe
                                                MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                (coe MAlonzo.Code.Once.IR.C_initial_76))
                                             (coe (0 :: Integer)) (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'morph'45'check_476
                                             v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_114 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5460 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5460 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Type.C__'43'__26 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                          (coe v3) (coe v8) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      du_withUnit_478
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_114
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                               (coe ("inl" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v7)
                                                      (coe
                                                         (\ v13 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_112
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_inl_54))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'morph'45'check_488
                                                                 v13))))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Internal.Type.C_Unit_20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Void_22
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Int_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Float_36
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_rigid_38 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5598 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5598 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Type.C__'43'__26 v8 v9
                             -> let v10
                                      = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                          (coe v3) (coe v9) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      du_withUnit_478
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_failure_114
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                               (coe ("inr" :: Data.Text.Text))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                      (coe v7)
                                                      (coe
                                                         (\ v13 ->
                                                            coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 C_success_112
                                                                 (coe
                                                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                                                    (coe
                                                                       MAlonzo.Code.Once.IR.C_inr_60))
                                                                 (coe (0 :: Integer))
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'morph'45'check_500
                                                                 v13))))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Internal.Type.C_Unit_20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Void_22
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Int_34
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_Float_36
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Internal.Type.C_rigid_38 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_114 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5734 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5734 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4880 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5752 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5752 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4972 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5770 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5770 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_5110 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5788 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5788 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_5248
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5806 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5806 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_5354
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5824 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5824 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5460 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5842 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5842 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_696 (coe v1) (coe v2)
             C_failure_90 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5598 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_5860 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'dispatch_5860 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_620
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_622
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_624
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_626
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_628
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_630
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_632
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_634
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit'45'var_50)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_638 v4
        -> coe
             du_inferElabV'45'RResolved'45'aux_4722 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_128 (coe v0))
                (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-other
d_checkElabV'45'RResolved'45'other_5904 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'other_5904 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_696 (coe v2) (coe v3)
             C_failure_90 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v7
                      -> case coe v7 of
                           []
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_114 (coe v6))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (:) v8 v9
                             -> case coe v9 of
                                  []
                                    -> coe
                                         du_checkElabV'45'RVar'45'poly'45'check'45'aux_2012 (coe v0)
                                         (coe v8) (coe v2) (coe v6)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_128
                                               (coe v0))
                                            (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_124
                                               (coe v0))
                                            (coe v8))
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_68
                                            (coe
                                               MAlonzo.Code.Once.Internal.Typing.Scope.d_polys_126
                                               (coe v0))
                                            (coe v8))
                                  (:) v10 v11
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe C_failure_114 (coe v6))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_5940 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'dispatch_5940 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_620
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5734 (coe v0) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_622
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5752 (coe v0) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_624
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5770 (coe v0) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_626
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5788 (coe v0)
             (coe v2) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_628
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5806 (coe v0)
             (coe v2) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_630
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5824 (coe v0) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_632
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5842 (coe v0) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_634
        -> coe du_embedOrSubsume_696 (coe v2) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_638 v6
        -> coe
             d_checkElabV'45'RResolved'45'other_5904 (coe v0) (coe v1) (coe v2)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 ~v0 ~v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 v2 v3
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 v0 v1
  = coe du_embedOrSubsume_696 (coe v0) (coe v1)
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_6030 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RFloat'45'aux_6030 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'RFloat'45'aux_6030 v0 v1 v2 v3 v5
du_checkElabV'45'RFloat'45'aux_6030 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RFloat'45'aux_6030 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
              (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) (coe v4) in
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
                                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                    (coe
                                       MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Float_36) v8
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_float_198
                                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                          (coe v1) (coe v2) (coe v3))))
                                 (coe (0 :: Integer)) (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'sub_664
                                 (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                 (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_42) v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_114
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v4)
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_6084 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RFloat'45'aux_6084 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RFloat'45'aux_6084 v0 v1 v2 v3
du_inferElabV'45'RFloat'45'aux_6084 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RFloat'45'aux_6084 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
         (coe
            MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
            (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_198
            (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
               (coe v1) (coe v2) (coe v3)))
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'float_42)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_6104 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPair_6104 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("pair" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v8
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
                                                               d_checkPairOn_6114 (coe v0) (coe v6)
                                                               (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_pairTarget_138
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
d_checkPairOn_6114 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairOn_6114 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_130
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> case coe v11 of
                           MAlonzo.Code.Once.Internal.Type.C__'42'__24 v14 v15
                             -> let v16
                                      = d_checkElabV_6366
                                          (coe v0) (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v13))
                                             (coe v14)) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                       -> case coe v17 of
                                            C_success_112 v19 v20 v21 v22
                                              -> let v23
                                                       = d_checkElabV_6366
                                                           (coe v0) (coe v2)
                                                           (coe
                                                              MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                              (coe v9)
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                 (coe
                                                                    MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
                                                                          MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                          (coe v19) (coe v26))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_fork''_488
                                                                          v19 v26 v20 v27)
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                             (coe v21) (coe v28)))
                                                                       (coe v29))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'morph'45'check_584
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
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'other_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_6126 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairLit_6126 v0 v1 v2 v3 v4
  = let v5 = d_checkElabV_6366 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                C_success_112 v8 v9 v10 v11
                  -> let v12 = d_checkElabV_6366 (coe v0) (coe v2) (coe v4) in
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
                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                              (coe v8) (coe v15))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v8 v15 v9
                                              v16)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'pair'45'lit'45'check_702
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
d_checkCase_6136 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCase_6136 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("case" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v8
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
                                                               d_checkCaseOn_6146 (coe v0) (coe v6)
                                                               (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_caseTarget_166
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
d_checkCaseOn_6146 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_148 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseOn_6146 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_158
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v12 v13
                      -> case coe v10 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                             -> coe
                                  d_checkCaseGo_6162 (coe v0) (coe v1) (coe v2) (coe v12) (coe v13)
                                  (coe v11) (coe v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'other_162
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_6162 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseGo_6162 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_checkElabV_6366
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                 (coe v5)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                C_success_112 v10 v11 v12 v13
                  -> let v14
                           = d_checkElabV_6366
                               (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
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
                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                              (coe v10) (coe v17))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v10
                                              v17 v11 v18)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v12)
                                                 (coe v19)))
                                           (coe v13))
                                        (coe
                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'case'45'copair'45'check_564
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
d_checkCompose_6172 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose_6172 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_114
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("compose" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v8
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
                                                               d_checkComposeOn_6182 (coe v0)
                                                               (coe v6) (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.TargetView.d_arrowTarget_192
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
d_checkComposeOn_6182 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkComposeOn_6182 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_184
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                      -> coe
                           d_checkCompose'45'g_6218 (coe v0) (coe v1) (coe v2) (coe v8)
                           (coe v10) (coe v12)
                           (coe d_elabGivenV_6192 (coe v0) (coe v2) (coe v8) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_188
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.elabGivenV
d_elabGivenV_6192 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenV_6192 v0 v1 v2 v3
  = let v4
          = coe
              du_given'45'infer_418 (coe v2) (coe v3)
              (coe d_inferElabV_6358 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v5
           -> coe
                d_elabGivenLeaf_2152 (coe v0) (coe v5) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_340
                   (coe v1))
                (coe d_inferElabV_6358 (coe v0) (coe v1))
         MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v5 v6
           -> coe
                d_elabGivenApp_6204 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_340
                   (coe v5))
                (coe d_inferElabV_6358 (coe v0) (coe v1))
         MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v5 v6
           -> let v7
                    = d_inferElabV_6358
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_extendNamedCtx_132
                           (coe v0) (coe v5) (coe v2))
                        (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v8 of
                          C_success_88 v10 v11 v12 v13 v14
                            -> case coe v11 of
                                 MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v16 v17
                                   -> let v18
                                            = d_decideLeq_1302
                                                (coe v16)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) in
                                      coe
                                        (case coe v18 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v19
                                             -> coe
                                                  du_withUnit_478
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        C_failure_260
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                           (coe ("lambda" :: Data.Text.Text))))
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe v3)
                                                  (coe
                                                     (\ v20 ->
                                                        coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_success_258 (coe v10) (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                v16 v12)
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v13))
                                                             (coe v14))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Typing.C_d'45'lam_834
                                                             v16 v20 v9)))
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_260
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_72
                                                        (coe v5)
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
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
d_elabGivenApp_6204 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabGivenApp_6204 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe du_given'45'infer_418 (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_316
           -> let v8
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_260
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                              (coe ("cata" :: Data.Text.Text))))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v9
                     -> let v10
                              = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                  (coe v9) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> coe
                                    du_given'45'cata_590 (coe v9) (coe v4) (coe v11)
                                    (coe d_inferElabV_6358 (coe v0) (coe v2))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       C_failure_260
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                          (coe ("cata" :: Data.Text.Text))))
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v8)
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_324
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_6192 (coe v0) (coe v10) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_6192
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
                                                               MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                               (coe v14) (coe v22))
                                                            (coe
                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                               (coe v15) (coe v23))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_fork''_488
                                                               v15 v23 v16 v24)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v17) (coe v25)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.Internal.Typing.C_d'45'pair_950
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
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_328
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v9 v10
                  -> let v11
                           = d_elabGivenV_6192 (coe v0) (coe v2) (coe v3) (coe v4) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 C_success_258 v14 v15 v16 v17 v18
                                   -> let v19
                                            = d_elabGivenV_6192
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
                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                               (coe v23)
                                                               (coe
                                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                  (coe
                                                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                  (coe v15)))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_comp''_452
                                                               v23 v15 v14 v24 v16)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v25) (coe v17)))
                                                            (coe v26))
                                                         (coe
                                                            MAlonzo.Code.Once.Internal.Typing.C_d'45'compose_854
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
         MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_332
           -> case coe v1 of
                MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  C_failure_260
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                     (coe ("case" :: Data.Text.Text))))
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Once.Internal.Type.C__'43'__26 v12 v13
                            -> let v14
                                     = d_elabGivenV_6192 (coe v0) (coe v10) (coe v12) (coe v4) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> case coe v15 of
                                           C_success_258 v17 v18 v19 v20 v21
                                             -> let v22
                                                      = d_elabGivenV_6192
                                                          (coe v0) (coe v2) (coe v13) (coe v4) in
                                                coe
                                                  (case coe v22 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                       -> case coe v23 of
                                                            C_success_258 v25 v26 v27 v28 v29
                                                              -> coe
                                                                   du_given'45'case'45'join_4320
                                                                   (coe v12) (coe v13) (coe v4)
                                                                   (coe v17) (coe v18) (coe v19)
                                                                   (coe v20) (coe v16) (coe v25)
                                                                   (coe v26) (coe v27) (coe v28)
                                                                   (coe v29) (coe v24)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Internal.Type.Join.d_join'63'_582
                                                                      (coe v17) (coe v25))
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
d_checkCompose'45'g_6218 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'g_6218 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v7 of
             C_success_258 v9 v10 v11 v12 v13
               -> let v14
                        = d_checkElabV_6366
                            (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
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
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v17)
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v17 v10 v9
                                           v18 v11)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v19)
                                              (coe v12)))
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'g_520
                                        v9 v17 v10 v8 v16)
                              C_failure_114 v17
                                -> coe
                                     d_checkCompose'45'f_6232 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_260 v9
               -> coe
                    d_checkCompose'45'f_6232 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_6232 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose'45'f_6232 v0 v1 v2 v3 v4 v5
  = let v6 = d_inferElabV_6358 (coe v0) (coe v1) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> let v9
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_78))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v7 of
                   C_success_88 v10 v11 v12 v13 v14
                     -> case coe v10 of
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v15 v16 v17
                            -> case coe v16 of
                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                          -> let v20
                                                   = coe
                                                       MAlonzo.Code.Once.Type.Sub.du_arr'45'aux_28
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
                                                          (coe v15) (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
                                                          (coe v17) (coe v4))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.Sub.d__'8849'π'63'__10
                                                          (coe v19) (coe v5)) in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                    -> if coe v21
                                                         then case coe v22 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                  -> let v24
                                                                           = d_checkElabV_6366
                                                                               (coe v0) (coe v2)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                  (coe v3)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
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
                                                                                              MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                                              (coe
                                                                                                 v11)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                                                 (coe
                                                                                                    v18)
                                                                                                 (coe
                                                                                                    v27)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_452
                                                                                              v11
                                                                                              v27
                                                                                              v15
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
                                                                                           MAlonzo.Code.Once.Internal.Typing.C_t'45'compose'45'check'45'f_544
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
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_78))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v9
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v9
                   _ -> coe v9)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_6240 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurry_6240 v0 v1 v2
  = coe
      d_checkCurryOn_6248 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_curryTarget_108 (coe v2))
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_6248 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_88 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurryOn_6248 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'at_100
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> case coe v11 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v14 v15 v16
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                                    -> let v19
                                             = d_checkElabV_6366
                                                 (coe v0) (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                    (coe
                                                       MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                                       (coe v9) (coe v14))
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v18))
                                                    (coe v16)) in
                                       coe
                                         (case coe v19 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                              -> case coe v20 of
                                                   C_success_112 v22 v23 v24 v25
                                                     -> coe
                                                          du_withUnit_478
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_114
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("curry" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                          (coe v13)
                                                          (coe
                                                             (\ v26 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     C_success_112 (coe v22)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Surface.Syntax.C_curry''_506
                                                                        v23)
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v24))
                                                                     (coe v25))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'curry'45'check_604
                                                                     v26 v21)))
                                                   C_failure_114 v22
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v20)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'other_104
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_6254 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferOut_6254 v0 v1
  = coe
      du_inferOutOn_2364 (coe v0)
      (coe d_inferElabV_6358 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_6262 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkIn_6262 v0 v1 v2
  = coe
      d_checkInOn_6270 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.TypeCheck.TargetView.d_inTarget_84 (coe v2))
-- Once.TypeCheck.Elaborate.checkInOn
d_checkInOn_6270 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_InTarget_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInOn_6270 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'at_76
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe
                    du_checkInGo_6280 (coe v0) (coe v1) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'other_80
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_6280 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo_6280 v0 v1 v2 v3 ~v4 = du_checkInGo_6280 v0 v1 v2 v3
du_checkInGo_6280 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo_6280 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = d_checkElabV_6366
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v2)
                        (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v2))) in
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
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                          (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                                    (MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62
                                       (coe v2)
                                       (coe
                                          MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_In_94
                                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                          (coe v2) (coe v4)))
                                    v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'In'45'app'45'check_712 v8
                                 v4 v7)
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_6288 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCata_6288 v0 v1 v2
  = coe
      d_checkCataOn_6296 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_cataTarget_22 (coe v2))
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_6296 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataOn_6296 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_14
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v7 v8 v9
               -> case coe v7 of
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v10
                      -> case coe v8 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                             -> coe
                                  du_checkCataGo_6310 (coe v0) (coe v1) (coe v10) (coe v9) (coe v12)
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_6310 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataGo_6310 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkCataGo_6310 v0 v1 v2 v3 v4 v5
du_checkCataGo_6310 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkCataGo_6310 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_6366
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                        (coe
                           MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v2)
                           (coe v3))
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                        (coe v3)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> case coe v8 of
                       C_success_112 v10 v11 v12 v13
                         -> coe
                              du_withUnit_478
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_failure_114
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                       (coe ("cata" :: Data.Text.Text))))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              (coe v4)
                              (coe
                                 (\ v14 ->
                                    coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_112
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v10 v6 v11)
                                         (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'cata'45'check_620
                                         v10 v14 v6 v9)))
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
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_6318 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAna_6318 v0 v1 v2
  = coe
      d_checkAnaOn_6326 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.d_anaTarget_54 (coe v2))
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_6326 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaOn_6326 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_loop'45'at_36
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> coe
                    du_checkLoop_6352
                    (coe
                       d_checkElabV_6366 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v8) (coe v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'at_46 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> case coe v11 of
                           MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v14 v15
                             -> coe
                                  du_checkAnaGo_6342 (coe v0) (coe v1) (coe v14) (coe v9) (coe v13)
                                  (coe v15) (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'other_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_6342 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkAnaGo_6342 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_checkAnaGo_6342 v0 v1 v2 v3 v4 v5 v6 v7
du_checkAnaGo_6342 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe
    MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkAnaGo_6342 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = d_checkElabV_6366
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v2)
                           (coe v3))) in
           coe
             (case coe v9 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                  -> case coe v10 of
                       C_success_112 v12 v13 v14 v15
                         -> coe
                              du_withUnit_478
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_failure_114
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                       (coe ("ana" :: Data.Text.Text))))
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              (coe v4)
                              (coe
                                 (\ v16 ->
                                    coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_112
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v12))
                                         (coe MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v12 v8 v13)
                                         (coe addInt (coe (1 :: Integer)) (coe v14)) (coe v15))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'ana'45'check_640
                                         v12 v16 v6 v8 v11)))
                       C_failure_114 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_114
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkLoop
d_checkLoop_6352 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkLoop_6352 ~v0 ~v1 ~v2 ~v3 v4 = du_checkLoop_6352 v4
du_checkLoop_6352 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkLoop_6352 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_112 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_112
                       (coe
                          MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v3 v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'loop'45'check_652 v3 v2)
             C_failure_114 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV
d_inferElabV_6358 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV_6358 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Syntax.C_RVar_36 v2
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_4842 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupLocal_246 (coe v0)
                (coe v2))
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_124 (coe v0))
                (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RQualified_38 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v2)
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v2
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_5860 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670 (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v2 v3
        -> coe
             du_inferElabV'45'RApp'45'dispatch_6474 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_340
                (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_24))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Syntax.C_RLet_46 v2 v3 v4
        -> coe
             du_inferElabV'45'RLet'45'aux_6412 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabV_6358 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v2 v3
        -> coe
             du_inferElabV'45'RPair'45'aux_2796
             (coe d_inferElabV_6358 (coe v0) (coe v2))
             (coe d_inferElabV_6358 (coe v0) (coe v3))
      MAlonzo.Code.Once.Internal.Syntax.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RDestruct'45'aux_6426 (coe v0) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe d_inferElabV_6358 (coe v0) (coe v2))
      MAlonzo.Code.Once.Internal.Syntax.C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'unit_46)
      MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                (coe
                   MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                   (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v2)
                (coe (0 :: Integer)) (coe (0 :: Integer)))
             (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_30)
      MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v2 v3 v4 v5
        -> coe
             du_inferElabV'45'RFloat'45'aux_6084 (coe v0) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.Internal.Syntax.C_RAnnot_58 v2 v3
        -> coe
             du_inferElabV'45'RAnnot'45'aux_2850 (coe v3)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v3))
             (coe d_checkElabV_6366 (coe v0) (coe v2) (coe v3))
      MAlonzo.Code.Once.Internal.Syntax.C_RBinOp_60 v2 v3 v4
        -> coe
             du_inferElabV'45'RBinOp'45'aux_3068 (coe v2)
             (coe d_inferElabV_6358 (coe v0) (coe v3))
             (coe d_inferElabV_6358 (coe v0) (coe v4))
      MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v3
        -> coe d_inferElabV'45'neg'45'dispatch_6388 (coe v0) (coe v3)
      MAlonzo.Code.Once.Internal.Syntax.C_RAna_64 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV
d_checkElabV_6366 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV_6366 v0 v1 v2
  = coe du_checkElabV'45'wf_6374 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-wf
d_checkElabV'45'wf_6374 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'wf_6374 v0 ~v1 v2 v3
  = du_checkElabV'45'wf_6374 v0 v2 v3
du_checkElabV'45'wf_6374 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'wf_6374 v0 v1 v2
  = let v3
          = coe
              du_embedOrSubsume_696 (coe v2)
              (coe d_inferElabV_6358 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Syntax.C_RVar_36 v4
           -> let v5
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_4842 (coe v0) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupLocal'45'go_162
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0))
                           (coe v4)
                           (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_named_120 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_122 (coe v0)))
                        (coe
                           MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_38
                           (coe
                              MAlonzo.Code.Once.Internal.Typing.Scope.d_imports_124 (coe v0))
                           (coe v4)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          C_success_88 v8 v9 v10 v11 v12
                            -> coe du_embedOrSubsume_696 (coe v2) (coe v5)
                          C_failure_90 v8
                            -> coe
                                 du_checkElabV'45'RVar'45'bbc'45'other'45'aux_6008 (coe v2) (coe v5)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40 v4
           -> coe
                d_checkElabV'45'RResolved'45'dispatch_5940 (coe v0) (coe v4)
                (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670 (coe v4))
                (coe d_inferElabV_6358 (coe v0) (coe v1))
         MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v4 v5
           -> coe
                du_checkElabV'45'RApp'45'dispatch_6486 (coe v0) (coe v4) (coe v5)
                (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_340
                   (coe v4))
         MAlonzo.Code.Once.Internal.Syntax.C_RLam_44 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_114
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_26))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                            -> let v12
                                     = d_checkElabV_6366
                                         (coe
                                            MAlonzo.Code.Once.Internal.Typing.Scope.d_extendNamedCtx_132
                                            (coe v0) (coe v4) (coe v7))
                                         (coe v5) (coe v9) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           C_success_112 v15 v16 v17 v18
                                             -> case coe v15 of
                                                  MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v20 v21
                                                    -> let v22
                                                             = d_decideLeq_1302
                                                                 (coe v20) (coe v10) in
                                                       coe
                                                         (case coe v22 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                              -> coe
                                                                   du_withUnit_478
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         C_failure_114
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                            (coe
                                                                               ("lambda"
                                                                                ::
                                                                                Data.Text.Text))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                   (coe v11)
                                                                   (coe
                                                                      (\ v24 ->
                                                                         coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_112
                                                                              (coe v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                                 v20 v16)
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v17))
                                                                              (coe v18))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'lam_686
                                                                              v20 v24 v14)))
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      C_failure_114
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_72
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
         MAlonzo.Code.Once.Internal.Syntax.C_RPair_48 v4 v5
           -> coe
                d_checkElabV'45'RPair'45'aux_6512 (coe v0) (coe v4) (coe v5)
                (coe v2) (coe d_classifyRPairTarget_54 (coe v2))
         MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v4
           -> coe d_checkElabV'45'RInt'45'aux_6502 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v4 v5 v6 v7
           -> coe
                du_checkElabV'45'RFloat'45'aux_6030 (coe v0) (coe v4) (coe v5)
                (coe v6) (coe v2)
         MAlonzo.Code.Once.Internal.Syntax.C_RUnaryOp_62 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_6402 (coe v0) (coe v5) (coe v2)
                (coe d_negOperandView_138 (coe v5))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_6382 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other_6382 v0 v1 v2
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_6464 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHead_570
         (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_6388 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'dispatch_6388 v0 v1
  = coe
      d_inferElabV'45'neg'45'aux_6394 (coe v0) (coe v1)
      (coe d_negOperandView_138 (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_6394 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'aux_6394 v0 v1 v2
  = case coe v2 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_190
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe (1 :: Integer)) (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Once.Internal.Typing.C_t'45'neg_136
                       (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_30))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                       (coe
                          MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_198
                          (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                             (coe
                                MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v7)
                                (coe v8) (coe v9))))
                       (coe (1 :: Integer)) (coe (0 :: Integer)))
                    (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'neg'45'float_148)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_inferElabV'45'RUnaryOp'45'aux_2890
             (coe d_inferElabV_6358 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_6402 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T_NegOperandView_116 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'dispatch_6402 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_120
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v5
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_2978 (coe v0) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_130
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v8 v9 v10 v11
               -> coe
                    du_checkElabV'45'neg'45'float'45'aux_3016 (coe v0) (coe v8)
                    (coe v9) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_134
        -> coe
             du_embedOrSubsume_696 (coe v2)
             (coe
                du_inferElabV'45'RUnaryOp'45'aux_2890
                (coe d_inferElabV_6358 (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_6412 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux_6412 v0 v1 ~v2 v3 v4
  = du_inferElabV'45'RLet'45'aux_6412 v0 v1 v3 v4
du_inferElabV'45'RLet'45'aux_6412 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux_6412 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_88 v6 v7 v8 v9 v10
               -> coe
                    du_inferElabV'45'RLet'45'aux2_4108 (coe v6) (coe v7) (coe v8)
                    (coe v9) (coe v5)
                    (coe
                       d_inferElabV_6358
                       (coe
                          MAlonzo.Code.Once.Internal.Typing.Scope.d_extendNamedCtx_132
                          (coe v0) (coe v1) (coe v6))
                       (coe v2))
             C_failure_90 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_6426 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'aux_6426 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferElabV'45'RDestruct'45'aux_6426 v0 v2 v3 v4 v5 v6
du_inferElabV'45'RDestruct'45'aux_6426 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'aux_6426 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_88 v8 v9 v10 v11 v12
               -> case coe v8 of
                    MAlonzo.Code.Once.Internal.Type.C_Unit_20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Void_22
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v13 v14
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxL_6454 (coe v0) (coe v3) (coe v4)
                           (coe v13) (coe v14) (coe v9) (coe v10) (coe v11) (coe v7)
                           (coe
                              d_inferElabV_6358
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_extendNamedCtx_132
                                 (coe v0) (coe v1) (coe v13))
                              (coe v2))
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Int_34
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_Float_36
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Internal.Type.C_rigid_38 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_90
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_6454 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxL_6454 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       v8 v9 v10 ~v11 v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_6454
      v0 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inferElabV'45'RDestruct'45'auxL_6454 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxL_6454 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             C_success_88 v12 v13 v14 v15 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.Internal.Context.C__'8759'__52 v18 v19
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxR_4422 (coe v3) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v8) (coe v12) (coe v18) (coe v19) (coe v14)
                           (coe v15) (coe v11)
                           (coe
                              d_inferElabV_6358
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_extendNamedCtx_132
                                 (coe v0) (coe v1) (coe v4))
                              (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_90 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_6464 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  Maybe
    MAlonzo.Code.Once.Internal.Typing.Scope.T_PolyBuiltinApp_260 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other'45'aux_6464 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'other'45'aux_6464 v0 v1 v2 v3
du_inferElabV'45'RApp'45'other'45'aux_6464 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  Maybe
    MAlonzo.Code.Once.Internal.Typing.Scope.T_PolyBuiltinApp_260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'other'45'aux_6464 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe
                      ("unreachable: ahv-other \8658 classifyAppHead nothing"
                       ::
                       Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v4 = d_inferElabV_6358 (coe v0) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Internal.Type.C_Unit_20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Void_22
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'42'__24 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'43'__26 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v12 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_fin_42 v17
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                                     -> let v18
                                                              = coe
                                                                  du_checkElabV'45'wf_6374 (coe v0)
                                                                  (coe v2) (coe v12) in
                                                        coe
                                                          (case coe v18 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                               -> case coe v19 of
                                                                    C_success_112 v21 v22 v23 v24
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_88 (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                                    (coe v15)
                                                                                    (coe v21)))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_app_50
                                                                                 v8 v21 v12 v15 v9
                                                                                 v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v10)
                                                                                 (coe v23))
                                                                              (coe v24))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'app_386
                                                                              v12 v15 v8 v21 v6 v20)
                                                                    C_failure_114 v21
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_90
                                                                              (coe v21))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                                     -> case coe v15 of
                                                          MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_90
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                       (coe v7)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_90
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                       (coe v7)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                            -> let v18
                                                                     = coe
                                                                         du_checkElabV'45'wf_6374
                                                                         (coe v0) (coe v2)
                                                                         (coe v12) in
                                                               coe
                                                                 (case coe v18 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                      -> case coe v19 of
                                                                           C_success_112 v21 v22 v23 v24
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_success_88
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                                        (coe v8)
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                                           (coe v15)
                                                                                           (coe
                                                                                              v21)))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_effApp_68
                                                                                        v8 v21 v12
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                                        v9 v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                        (coe v10)
                                                                                        (coe v23))
                                                                                     (coe v24))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_406
                                                                                     v12 v8 v21
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                                     v6 v20)
                                                                           C_failure_114 v21
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_failure_90
                                                                                     (coe v21))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_90
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_90
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                     -> let v17
                                                              = coe
                                                                  du_checkElabV'45'wf_6374 (coe v0)
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
                                                                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                                                                 (coe v13)
                                                                                 (coe v14))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                                 (coe v8)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                                    (coe v15)
                                                                                    (coe v20)))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_effApp_68
                                                                                 v8 v20 v12
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                                 v9 v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v10)
                                                                                 (coe v22))
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Internal.Typing.C_t'45'effApp_406
                                                                              v12 v8 v20
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                              v6 v19)
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
                              MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Int_34
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Float_36
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_rigid_38 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_90
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_90 v7
                         -> coe
                              du_inferSpine_6494 (coe v0) (coe v1)
                              (coe d_inferElabV_6358 (coe v0) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_6474 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'dispatch_6474 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'dispatch_6474 v0 v1 v2 v3
du_inferElabV'45'RApp'45'dispatch_6474 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'dispatch_6474 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_296
        -> let v4 = d_inferElabV_6358 (coe v0) (coe v2) in
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
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                          (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_id_20) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_282 v8 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_298
        -> coe
             du_inferFstOn_2440 (coe v0)
             (coe d_inferElabV_6358 (coe v0) (coe v2))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_300
        -> coe
             du_inferSndOn_2516 (coe v0)
             (coe d_inferElabV_6358 (coe v0) (coe v2))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_302
        -> let v4 = d_inferElabV_6358 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_88 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                 (coe
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                          (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_terminal_72) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_316 v7 v8
                                 v6)
                       C_failure_90 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inl_304
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_28))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inr_306
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_30))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_308
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_32))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'curry_310
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'apply_312
        -> coe
             du_inferApplyOn_2766 (coe v0)
             (coe d_inferElabV_6358 (coe v0) (coe v2))
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'In_314
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_316
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'ana_318
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'Out_320
        -> coe d_inferOut_6254 (coe v0) (coe v2)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_324
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_328
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_332
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_90
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'other_336
        -> coe
             d_inferElabV'45'RApp'45'other_6382 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_6486 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'dispatch_6486 v0 v1 v2 v3 v4 ~v5
  = du_checkElabV'45'RApp'45'dispatch_6486 v0 v1 v2 v3 v4
du_checkElabV'45'RApp'45'dispatch_6486 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'dispatch_6486 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'id_296
        -> let v5 = d_inferElabV_6358 (coe v0) (coe v2) in
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
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_id_20) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'id'45'app_282 v9
                                         v7) in
                            coe (coe du_embedOrSubsume_696 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'fst_298
        -> let v5
                 = coe
                     du_inferFstOn_2440 (coe v0)
                     (coe d_inferElabV_6358 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_696 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'snd_300
        -> let v5
                 = coe
                     du_inferSndOn_2516 (coe v0)
                     (coe d_inferElabV_6358 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_696 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'terminal_302
        -> let v5 = d_inferElabV_6358 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_88
                                         (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                         (coe
                                            MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                               (coe
                                                  MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_terminal_72) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'app_316
                                         v8 v9 v7) in
                            coe (coe du_embedOrSubsume_696 (coe v3) (coe v13))
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inl_304
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_6374 (coe v0) (coe v2) (coe v5) in
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
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                              (coe
                                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v10
                                           v5 (coe MAlonzo.Code.Once.IR.C_inl_54) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'inl'45'app'45'check_736
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'inr_306
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C_Unit_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Void_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_6374 (coe v0) (coe v2) (coe v6) in
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
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                              (coe
                                                 MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v10
                                           v6 (coe MAlonzo.Code.Once.IR.C_inr_60) v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'inr'45'app'45'check_748
                                        v10 v9)
                              C_failure_114 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Int_34
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_Float_36
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Internal.Type.C_rigid_38 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_114
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'initial_308
        -> let v5
                 = coe
                     du_checkElabV'45'wf_6374 (coe v0) (coe v2)
                     (coe MAlonzo.Code.Once.Internal.Type.C_Void_22) in
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
                                    MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                       (coe
                                          MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                          (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                                    (coe MAlonzo.Code.Once.Internal.Type.C_Void_22)
                                    (coe MAlonzo.Code.Once.IR.C_initial_76) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Internal.Typing.C_t'45'initial'45'app'45'check_758
                                 v8 v7)
                       C_failure_114 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'curry_310
        -> coe d_checkCurry_6240 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'apply_312
        -> let v5
                 = coe
                     du_inferApplyOn_2766 (coe v0)
                     (coe d_inferElabV_6358 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_696 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'In_314
        -> coe d_checkIn_6262 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'cata_316
        -> coe d_checkCata_6288 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'ana_318
        -> coe d_checkAna_6318 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'Out_320
        -> let v5
                 = coe
                     du_inferOutOn_2364 (coe v0)
                     (coe d_inferElabV_6358 (coe v0) (coe v2)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_88 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_696 (coe v3) (coe v5)
                       C_failure_90 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'pair'45'applied_324
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v6 v7
               -> coe
                    d_checkPair_6104 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
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
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'compose'45'applied_328
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v6 v7
               -> coe
                    d_checkCompose_6172 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
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
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'case'45'applied_332
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Syntax.C_RApp_42 v6 v7
               -> coe
                    d_checkCase_6136 (coe v0)
                    (coe
                       MAlonzo.Code.Once.Internal.Syntax.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.Internal.Syntax.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.Spec.Name.C_canonical_12
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
      MAlonzo.Code.Once.Internal.Typing.Scope.C_ahv'45'other_336
        -> let v6
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_6474 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_340
                        (coe v1)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_88 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_696 (coe v3) (coe v6)
                       C_failure_90 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_114 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_6494 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferSpine_6494 v0 v1 ~v2 ~v3 v4 = du_inferSpine_6494 v0 v1 v4
du_inferSpine_6494 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferSpine_6494 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_88 v5 v6 v7 v8 v9
               -> let v10
                        = d_elabGivenV_6192
                            (coe v0) (coe v1) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Spec.Grade.C_fin_42
                               (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)) in
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
                                           MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                           (coe v14)
                                           (coe
                                              MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v6)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_50 v14 v6 v5
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v15 v7)
                                        (coe
                                           addInt (coe (1 :: Integer))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16)
                                              (coe v8)))
                                        (coe v17))
                                     (coe
                                        MAlonzo.Code.Once.Internal.Typing.C_t'45'app'45'spine_422 v5
                                        v14 v6 v4 v12)
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
d_checkElabV'45'RInt'45'aux_6502 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RInt'45'aux_6502 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_success_88 (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                 (coe
                    MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                    (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118 (coe v0)))
                 (coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v1)
                 (coe (0 :: Integer)) (coe (0 :: Integer)))
              (coe MAlonzo.Code.Once.Internal.Typing.C_t'45'int_30) in
    coe (coe du_embedOrSubsume_696 (coe v2) (coe v3))
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_6512 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  T_RPairTarget_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RPair'45'aux_6512 v0 v1 v2 v3 v4
  = case coe v4 of
      C_rpt'45'prod_36
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
               -> coe
                    d_checkPairLit_6126 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_46
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_114
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13))
                                    (coe v11))
                                 (coe v11)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'other_50
        -> let v6
                 = coe
                     du_inferElabV'45'RPair'45'aux_2796
                     (coe d_inferElabV_6358 (coe v0) (coe v1))
                     (coe d_inferElabV_6358 (coe v0) (coe v2)) in
           coe (coe du_embedOrSubsume_696 (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_10048 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab_10048 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inferElabV_6358 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_10062 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_CheckElabResult_98
d_checkElab_10062 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_checkElabV_6366 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_10080 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkApply_10080 v0 v1 v2
  = let v3 = d_inferElabV_6358 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                C_success_88 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Internal.Type.C_Unit_20
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_Void_22
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C__'42'__24 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Internal.Type.C_Unit_20
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Void_22
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'42'__24 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'43'__26 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v18
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_114
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_114
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_One_10
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v18
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_114
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_114
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42 v18
                                                     -> case coe v18 of
                                                          MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                                            -> let v19
                                                                     = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                                                         (coe v13) (coe v12) in
                                                               coe
                                                                 (let v20
                                                                        = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                                                                            (coe v2) (coe v15) in
                                                                  coe
                                                                    (case coe v19 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                         -> if coe v21
                                                                              then coe
                                                                                     seq (coe v22)
                                                                                     (case coe
                                                                                             v20 of
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                          -> if coe
                                                                                                  v23
                                                                                               then coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v24)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            C_success_112
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Internal.Context.d_zeroUsage_56
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Internal.Typing.Scope.d_size_118
                                                                                                                     (coe
                                                                                                                        v0)))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                                                                                                  (coe
                                                                                                                     v16)
                                                                                                                  (coe
                                                                                                                     v7)))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434
                                                                                                               v7
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Internal.Type.C__'42'__24
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
                                                                                                            MAlonzo.Code.Once.Internal.Typing.C_t'45'apply'45'check_724
                                                                                                            v13
                                                                                                            v7
                                                                                                            v5))
                                                                                               else coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v24)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            C_failure_114
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                                                               (coe
                                                                                                                  v2)
                                                                                                               (coe
                                                                                                                  v15)))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                              else coe
                                                                                     seq (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           C_failure_114
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                              (coe
                                                                                                 ("apply"
                                                                                                  ::
                                                                                                  Data.Text.Text))))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_114
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                       (coe
                                                                          ("apply"
                                                                           ::
                                                                           Data.Text.Text))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_114
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Int_34
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_Float_36
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Internal.Type.C_rigid_38 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Internal.Type.C__'43'__26 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v11 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_Int_34
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_Float_36
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Internal.Type.C_rigid_38 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_114
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
d_inferElab'45'RApp'45'other_10350 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  T_InferElabResult_74
d_inferElab'45'RApp'45'other_10350 v0 v1 v2
  = let v3
          = coe
              du_asFun_1124
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe d_inferElabV_6358 (coe v0) (coe v1))) in
    coe
      (case coe v3 of
         C_isFun_1104 v4 v5 v6 v7 v8 v9 v10
           -> let v11
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe du_checkElabV'45'wf_6374 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v11 of
                   C_success_112 v12 v13 v14 v15
                     -> coe
                          C_success_88 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88 (coe v5)
                                (coe v12)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_app_50 v7 v12 v4 v5 v8 v13)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9) (coe v14))
                          (coe v15)
                   C_failure_114 v12 -> coe C_failure_90 (coe v12)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_isEff_1116 v4 v5 v6 v7 v8 v9 v10 v11
           -> let v12
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe du_checkElabV'45'wf_6374 (coe v0) (coe v2) (coe v6)) in
              coe
                (case coe v12 of
                   C_success_112 v13 v14 v15 v16
                     -> coe
                          C_success_88
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe v7))
                          (coe
                             MAlonzo.Code.Once.Internal.Context.du__'43''7512'__76 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du__'42''7512'__88
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v13)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v8 v13 v6 v5 v9 v14)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10) (coe v15))
                          (coe v16)
                   C_failure_114 v13 -> coe C_failure_90 (coe v13)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_notFun_1118 v4 -> coe C_failure_90 (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
