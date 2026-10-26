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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Concrete
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Determined
import qualified MAlonzo.Code.Once.Type.Grade
import qualified MAlonzo.Code.Once.Type.Join
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.MatchCorrect
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.Type.SubDecide
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Scope
import qualified MAlonzo.Code.Once.TypeCheck.TargetView
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.isRIntVliftTarget?
d_isRIntVliftTarget'63'_12 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRIntVliftTarget'63'_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Spec.Type.C_Int_32
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
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRFloatVliftTarget'63'_24 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Spec.Type.C_Float_34
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
d_RPairTarget_32 a0 a1 = ()
data T_RPairTarget_32
  = C_rpt'45'prod_40 | C_rpt'45'vlift_50 | C_rpt'45'other_54
-- Once.TypeCheck.Elaborate.classifyRPairTarget
d_classifyRPairTarget_60 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_RPairTarget_32
d_classifyRPairTarget_60 ~v0 v1 = du_classifyRPairTarget_60 v1
du_classifyRPairTarget_60 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_RPairTarget_32
du_classifyRPairTarget_60 v0
  = let v1 = coe C_rpt'45'other_54 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
           -> coe C_rpt'45'prod_40
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v4 of
                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
                                -> coe C_rpt'45'vlift_50
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_82 a0 a1 a2 = ()
data T_InferElabResult_82
  = C_success_98 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_100 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_110 a0 a1 a2 a3 = ()
data T_CheckElabResult_110
  = C_success_126 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_128 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.NegOperandView
d_NegOperandView_130 a0 = ()
data T_NegOperandView_130
  = C_nov'45'int_134 | C_nov'45'float_142 | C_nov'45'other_146
-- Once.TypeCheck.Elaborate.negOperandView
d_negOperandView_150 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_NegOperandView_130
d_negOperandView_150 v0
  = let v1 = coe C_nov'45'other_146 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v2
           -> coe C_nov'45'int_134
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v2 v3 v4
           -> coe C_nov'45'float_142
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.GivenElabResult
d_GivenElabResult_172 a0 a1 a2 a3 a4 = ()
data T_GivenElabResult_172
  = C_success_192 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                  MAlonzo.Code.Once.Spec.Context.T_Usage_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_194 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_220 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
d_given'45'infer'45'dec_220 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = du_given'45'infer'45'dec_220
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_given'45'infer'45'dec_220 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
du_given'45'infer'45'dec_220 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
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
                                                C_success_192 (coe v3) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                      (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                         (coe v5))
                                                      (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v14
                                                      (coe
                                                         MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32
                                                         (coe v3))
                                                      v17)
                                                   v7)
                                                (coe v8) (coe v9)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v16)
                                         (coe
                                            C_failure_194
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                  (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v4))
                                                  (coe v3))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                  (coe v2)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                     (coe v5))
                                                  (coe v3))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v13)
                    (coe
                       C_failure_194
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                             (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-infer
d_given'45'infer_296 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
d_given'45'infer_296 v0 ~v1 ~v2 v3 v4 v5
  = du_given'45'infer_296 v0 v3 v4 v5
du_given'45'infer_296 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
du_given'45'infer_296 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> let v9
                 = coe
                     C_failure_194
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
                  -> case coe v11 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                         -> case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     du_given'45'infer'45'dec_220 (coe v0) (coe v1) (coe v10)
                                     (coe v12) (coe v2) (coe v14) (coe v5) (coe v6) (coe v7)
                                     (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                        (coe v0) (coe v1) (coe v10))
                                     (coe
                                        MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
                                        (coe v14) (coe v2))
                              _ -> coe v9
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v9)
      C_failure_100 v4 -> coe C_failure_194 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.withUnit
d_withUnit_352 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit_352 ~v0 v1 v2 v3 = du_withUnit_352 v1 v2 v3
du_withUnit_352 ::
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit_352 v0 v1 v2
  = coe
      du_withUnit'45'aux_358 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (coe v1))
      (coe v2)
-- Once.TypeCheck.Elaborate.withUnit-aux
d_withUnit'45'aux_358 ::
  () ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'aux_358 ~v0 ~v1 v2 v3 v4
  = du_withUnit'45'aux_358 v2 v3 v4
du_withUnit'45'aux_358 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'aux_358 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v2 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v4) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-dec
d_given'45'cata'45'dec_402 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
d_given'45'cata'45'dec_402 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10
                           v11 v12 v13
  = du_given'45'cata'45'dec_402 v1 v4 v5 v7 v9 v10 v11 v12 v13
du_given'45'cata'45'dec_402 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
du_given'45'cata'45'dec_402 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       du_withUnit_352
                       (coe
                          C_failure_194
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                             (coe ("cata" :: Data.Text.Text))))
                       (coe v1)
                       (coe
                          (\ v11 ->
                             coe
                               C_success_192 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v4
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v0)) v2 v5)
                               (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))))
             else coe
                    seq (coe v10)
                    (coe
                       C_failure_194
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("cata" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_466 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
d_given'45'cata_466 v0 v1 ~v2 v3 v4 v5 v6
  = du_given'45'cata_466 v0 v1 v3 v4 v5 v6
du_given'45'cata_466 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
du_given'45'cata_466 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_98 v6 v7 v8 v9 v10
        -> let v11
                 = coe
                     C_failure_194
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                        (coe ("cata" :: Data.Text.Text))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                  -> coe
                       du_given'45'cata'45'dec_402 (coe v1) (coe v3) (coe v4) (coe v14)
                       (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe
                          MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe v0) (coe v6)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                             (coe
                                MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v2)
                                (coe v14))
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                             (coe v14)))
                _ -> coe v11)
      C_failure_100 v6 -> coe C_failure_194 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_532 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_embedOrSubsume'45'dec_532 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'dec_532 v0 v3 v4 v5 v6 v7 v8 v9
du_embedOrSubsume'45'dec_532 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
du_embedOrSubsume'45'dec_532 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           C_success_126 (coe v1)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v3 v10 v4)
                           (coe v5) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_572 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_embedOrSubsume_572 v0 ~v1 ~v2 v3 v4
  = du_embedOrSubsume_572 v0 v3 v4
du_embedOrSubsume_572 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
du_embedOrSubsume_572 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_embedOrSubsume'45'dec_532 (coe v0) (coe v4) (coe v1) (coe v3)
             (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170 (coe v0)
                (coe v3) (coe v1))
      C_failure_100 v3 -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_602 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specId_602 ~v0 ~v1 = du_specId_602
du_specId_602 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specId_602
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_612 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specFst_612 ~v0 ~v1 ~v2 = du_specFst_612
du_specFst_612 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specFst_612
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_624 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specSnd_624 ~v0 ~v1 ~v2 = du_specSnd_624
du_specSnd_624 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specSnd_624
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_636 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInl_636 ~v0 ~v1 ~v2 = du_specInl_636
du_specInl_636 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInl_636
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_648 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInr_648 ~v0 ~v1 ~v2 = du_specInr_648
du_specInr_648 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInr_648
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_654 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specUnitGen_654 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
-- Once.TypeCheck.Elaborate.specPair
d_specPair_664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specPair_664 v0 ~v1 ~v2 = du_specPair_664 v0
du_specPair_664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specPair_664 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
               MAlonzo.Code.Once.Surface.Syntax.C_pair_86
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_54
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_54
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_676 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specTerminal_676 ~v0 ~v1 = du_specTerminal_676
du_specTerminal_676 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specTerminal_676
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_684 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInitial_684 ~v0 ~v1 = du_specInitial_684
du_specInitial_684 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInitial_684
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_696 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCurry_696 v0 v1 ~v2 = du_specCurry_696 v0 v1
du_specCurry_696 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCurry_696 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
               MAlonzo.Code.Once.Surface.Syntax.C_app_54
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_20
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_86
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_710 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specApply_710 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
         (coe
            MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_54
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__40
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
            (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__40
            (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
            (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))
         v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_20
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_110
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Spec.Grade.C_fin_42
                     (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
               (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_20
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_724 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCompose_724 v0 v1 ~v2 = du_specCompose_724 v0 v1
du_specCompose_724 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCompose_724 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_38
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
               MAlonzo.Code.Once.Surface.Syntax.C_app_54
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               v1 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_20
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_54
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specCase
d_specCase_740 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCase_740 v0 v1 ~v2 = du_specCase_740 v0 v1
du_specCase_740 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCase_740 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38
      (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
         (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
         (coe
            MAlonzo.Code.Once.Type.Grade.d__'8852'q__20
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_38
         (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
            (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
            (coe
               MAlonzo.Code.Once.Type.Grade.d__'8852'q__20
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_38
            (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
               (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
               (coe
                  MAlonzo.Code.Once.Type.Grade.d__'8852'q__20
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
               MAlonzo.Code.Once.Surface.Syntax.C_case''_156
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                  (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                        (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (MAlonzo.Code.Once.Spec.Grade.d__'43'q__14
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.d__'42'q__18
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)))
                        (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
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
                  MAlonzo.Code.Once.Surface.Syntax.C_var_20
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_54
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                              (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                              (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36)))))
                  v0 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_54
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                     (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                        (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
                              (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36)))))
                  v1 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_20
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.extract-morph-aux
d_extract'45'morph'45'aux_766 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph'45'aux_766 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_extract'45'morph'45'aux_766 v4 v8
du_extract'45'morph'45'aux_766 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_766 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_786 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_786 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_extract'45'morph_786 v4 v5 v6 v7
du_extract'45'morph_786 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_786 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_766
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_796 a0 a1 a2 = ()
data T_WellFormedFView_796
  = C_wfv'45'yes_806 MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_wfv'45'no_808
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_816 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_796
d_inspectWellFormedF_816 ~v0 v1 v2
  = du_inspectWellFormedF_816 v1 v2
du_inspectWellFormedF_816 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_796
du_inspectWellFormedF_816 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468 (coe v0)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_wfv'45'yes_806 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_808
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_838 = ()
data T_AppSpine_838
  = C_mkSpine_848 MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
                  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_844 ::
  T_AppSpine_838 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_head_844 v0
  = case coe v0 of
      C_mkSpine_848 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_846 ::
  T_AppSpine_838 -> [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68]
d_args_846 v0
  = case coe v0 of
      C_mkSpine_848 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_850 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> T_AppSpine_838
d_spineOf_850 v0
  = coe
      du_go_858 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_858 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68] -> T_AppSpine_838
d_go_858 ~v0 v1 v2 = du_go_858 v1 v2
du_go_858 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68] -> T_AppSpine_838
du_go_858 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v2
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v2 v3
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v2
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v2 v3
        -> coe
             du_go_858 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v2 v3
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v2 v3 v4
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v2 v3
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v2 v3 v4 v5 v6
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v2
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v2 v3 v4
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v2 v3
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v2 v3 v4
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v2
        -> coe C_mkSpine_848 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_944 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_944 v0
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
d_matchInferResult_954 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_matchInferResult_954 v0 ~v1 ~v2 v3 v4
  = du_matchInferResult_954 v0 v3 v4
du_matchInferResult_954 ::
  Integer ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_matchInferResult_954 v0 v1 v2
  = case coe v1 of
      C_success_98 v3 v4 v5 v6 v7
        -> let v8
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                     (coe v0) (coe v2) (coe v3) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe
                              seq (coe v10)
                              (coe C_success_126 (coe v4) (coe v5) (coe v6) (coe v7))
                       else coe
                              seq (coe v10)
                              (coe
                                 C_failure_128
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                    (coe v2) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_100 v3 -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1004 a0 a1 a2 = ()
data T_FunProjection_1004
  = C_isFun_1020 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_isEff_1032 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                 MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notFun_1034 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1042 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_FunProjection_1004
d_asFun_1042 v0 ~v1 ~v2 v3 = du_asFun_1042 v0 v3
du_asFun_1042 ::
  Integer -> T_InferElabResult_82 -> T_FunProjection_1004
du_asFun_1042 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                    -> coe
                                         C_isFun_1020 (coe v7) (coe v10) (coe v9) (coe v3) (coe v4)
                                         (coe v5) (coe v6)
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_notFun_1034
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_notFun_1034
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_isEff_1032 (coe v11)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                (coe v7) (coe v9) (coe v3) (coe v4) (coe v5)
                                                (coe v6)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         C_notFun_1034
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         C_notFun_1034
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         C_isEff_1032 (coe v11)
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) (coe v7)
                                         (coe v9) (coe v3) (coe v4) (coe v5) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notFun_1034
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                       (coe (0 :: Integer)) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notFun_1034 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1132 a0 a1 a2 = ()
data T_IntProjection_1132
  = C_isInt_1142 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notInt_1144 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_IntProjection_1132
d_asInt_1152 v0 ~v1 ~v2 v3 = du_asInt_1152 v0 v3
du_asInt_1152 ::
  Integer -> T_InferElabResult_82 -> T_IntProjection_1132
du_asInt_1152 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe C_isInt_1142 (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notInt_1144
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notInt_1144 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1192 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1192 v0 ~v1 ~v2 v3 = du_notNumeric_1192 v0 v3
du_notNumeric_1192 ::
  Integer ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1192 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1222 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1222 v0 v1
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
d_inferElab'45'RApp'45'id_1228 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElab'45'RApp'45'id_1228 ~v0 v1 v2
  = du_inferElab'45'RApp'45'id_1228 v1 v2
du_inferElab'45'RApp'45'id_1228 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElab'45'RApp'45'id_1228 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             C_success_98 (coe v2)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                (coe
                   MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                   (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_1248 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_1248 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_1292 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.Poly.T_ArrowSchema_314 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
d_given'45'poly'45'k_1292 ~v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20
  = du_given'45'poly'45'k_1292 v1 v2 v3 v4 v6 v7 v19 v20
du_given'45'poly'45'k_1292 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
du_given'45'poly'45'k_1292 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       C_success_192 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                             (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v2))
                             (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v3))
                             v6)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v1))
                       (coe (0 :: Integer)) (coe (0 :: Integer)))
             else coe seq (coe v9) (coe C_failure_194 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-π
d_given'45'poly'45'π_1378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.Poly.T_ArrowSchema_314 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
d_given'45'poly'45'π_1378 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_given'45'poly'45'π_1378 v0 v1 v2 v3 v5 v6 v8 v9 v18 v20
du_given'45'poly'45'π_1378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
du_given'45'poly'45'π_1378 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> if coe v10
             then case coe v11 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                      -> coe
                           du_given'45'poly'45'k_1292 (coe v1) (coe v2) (coe v3)
                           (coe
                              MAlonzo.Code.Once.Type.Poly.d_substPoly_186 (coe v0) (coe v8)
                              (coe v6))
                           (coe v7) (coe v4) (coe v12)
                           (coe
                              MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.Type.Poly.d_substPoly_186 (coe v0) (coe v8)
                                    (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v11) (coe C_failure_194 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-m
d_given'45'poly'45'm_1466 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.Poly.T_ArrowSchema_314 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_GivenElabResult_172
d_given'45'poly'45'm_1466 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_given'45'poly'45'm_1466 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v18
du_given'45'poly'45'm_1466 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_GivenElabResult_172
du_given'45'poly'45'm_1466 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> coe
             du_given'45'poly'45'π_1378 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5) (coe v6) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Type.MatchCorrect.du_instantiate'45'sound_1850
                   (coe v0) (coe v7) (coe v3) (coe v11)))
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10 (coe v9)
                (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_failure_194 (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-d
d_given'45'poly'45'd_1544 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.Poly.T_ArrowSchema_314 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
d_given'45'poly'45'd_1544 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 v17
  = du_given'45'poly'45'd_1544 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v17
du_given'45'poly'45'd_1544 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_172
du_given'45'poly'45'd_1544 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then coe
                    seq (coe v12)
                    (coe
                       du_given'45'poly'45'm_1466 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.Type.Match.d_instantiate_100 (coe v0) (coe v7)
                          (coe v3)))
             else coe seq (coe v12) (coe C_failure_194 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1608 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_172
d_given'45'poly'45'a_1608 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 v13
  = du_given'45'poly'45'a_1608 v0 v1 v2 v3 v4 v5 v6 v13
du_given'45'poly'45'a_1608 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_172
du_given'45'poly'45'a_1608 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  du_given'45'poly'45'd_1544 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6) (coe v9) (coe v11) (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_608
                                     (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_failure_194 (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-g
d_given'45'poly'45'g_1674 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_GivenElabResult_172
d_given'45'poly'45'g_1674 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 v12 ~v13
  = du_given'45'poly'45'g_1674 v0 v1 v2 v3 v4 v5 v6 v12
du_given'45'poly'45'g_1674 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_GivenElabResult_172
du_given'45'poly'45'g_1674 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe C_failure_194 (coe v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             seq (coe v8)
             (coe
                du_given'45'poly'45'a_1608 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_626 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1732 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_GivenElabResult_172
d_given'45'poly_1732 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 v10 ~v11
  = du_given'45'poly_1732 v0 v1 v2 v3 v4 v5 v6 v8 v10
du_given'45'poly_1732 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_172
du_given'45'poly_1732 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe C_failure_194 (coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe C_failure_194 (coe v5)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  seq (coe v11)
                                  (coe
                                     du_given'45'poly'45'g_1674 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v10)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_194 (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-res
d_given'45'res_1796 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
d_given'45'res_1796 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_98 v6 v7 v8 v9 v10
        -> coe du_given'45'infer_296 (coe v0) (coe v3) (coe v4) (coe v5)
      C_failure_100 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v7
               -> case coe v7 of
                    [] -> coe C_failure_194 (coe v6)
                    (:) v8 v9
                      -> case coe v9 of
                           []
                             -> coe
                                  du_given'45'poly_1732 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                                  (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                                     (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v1))
                                     (coe v8))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupPolyPrefix_74
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v1))
                                     (coe v8))
                           (:) v10 v11 -> coe C_failure_194 (coe v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-inst-aux
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 ~v0 v1 v2 ~v3 v4
                                                 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 v1 v2 v4 v12
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v1)
                       (coe (0 :: Integer)) (coe (0 :: Integer)))
             else coe seq (coe v5) (coe C_failure_128 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-ground-aux
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904 v0 v1 v2 v3 v4
                                                   v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904
      v0 v1 v2 v3 v4 v5 v11
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904 v0 v1 v2 v3 v4
                                                    v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe C_failure_128 (coe v4)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             seq (coe v7)
             (coe
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1850 (coe v1) (coe v2)
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                   (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                   (coe v5) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1956 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1956 v0 v1 v2 v3 v4 v5
                                                  ~v6 v7 ~v8 v9 ~v10
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_1956
      v0 v1 v2 v3 v4 v5 v7 v9
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1956 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1956 v0 v1 v2 v3 v4
                                                   v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe C_failure_128 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe C_failure_128 (coe v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  seq (coe v10)
                                  (coe
                                     du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1904 (coe v0)
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_128 (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6 ~v7 v8 ~v9
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014
      v0 v1 v2 v5 v8
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             C_success_98
             (coe
                MAlonzo.Code.Once.Type.Poly.d_extractGround_54 (coe v0) (coe v3)
                (coe v5))
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v2)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             seq (coe v5)
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 v0 v1 v2 v5
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2014 (coe v0)
                    (coe v1) (coe v2) (coe v5)
                    (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-aux
d_inferElabV'45'RVar'45'poly'45'aux_2084 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'aux_2084 v0 v1 v2 ~v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'aux_2084 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'aux_2084 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'aux_2084 v0 v1 v2
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2054 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_10
         (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v1))
         (coe v2))
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_2104 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
d_elabGivenLeaf_2104 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_given'45'res_1796
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
           -> coe
                du_withUnit_352
                (coe
                   C_failure_194
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                      (coe ("id" :: Data.Text.Text))))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        C_success_192 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                           (coe MAlonzo.Code.Once.IR.C_id_20))
                        (coe (0 :: Integer)) (coe (0 :: Integer))))
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
           -> let v8
                    = coe
                        C_failure_194
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                           (coe ("fst" :: Data.Text.Text))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_352
                          (coe
                             C_failure_194
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                (coe ("fst" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  C_success_192 (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
           -> let v8
                    = coe
                        C_failure_194
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                           (coe ("snd" :: Data.Text.Text))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_352
                          (coe
                             C_failure_194
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                (coe ("snd" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  C_success_192 (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_snd_48))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
           -> coe
                du_withUnit_352
                (coe
                   C_failure_194
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                      (coe ("terminal" :: Data.Text.Text))))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        C_success_192 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                           (coe MAlonzo.Code.Once.IR.C_terminal_72))
                        (coe (0 :: Integer)) (coe (0 :: Integer))))
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
           -> let v8
                    = coe
                        C_failure_194
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                           (coe ("initial" :: Data.Text.Text))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C_Void_20
                     -> coe
                          du_withUnit_352
                          (coe
                             C_failure_194
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                (coe ("initial" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v9 ->
                                coe
                                  C_success_192 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_initial_76))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_2178 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_2178 ~v0 ~v1 v2 ~v3 v4 = du_outIR_2178 v2 v4
du_outIR_2178 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_2178 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (coe
         MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v0)
         (coe v1))
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_2208 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferOutGo_2208 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inferOutGo_2208 v0 v1 v3 v4 v5 v6 v7 v8 v9
du_inferOutGo_2208 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82
du_inferOutGo_2208 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    C_success_98
                    (coe
                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v2)
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3)))
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v4
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))
                       (coe du_outIR_2178 (coe v2) (coe v9)) v5)
                    (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    C_success_98
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                       (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                          (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v3)))
                       (coe
                          MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))))
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v4
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))
                       (coe
                          MAlonzo.Code.Once.IR.C_curry_84
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe v0)
                                (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3)))
                             (coe du_outIR_2178 (coe v2) (coe v9))
                             (coe MAlonzo.Code.Once.IR.C_fst_42)))
                       v5)
                    (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("Out" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutAt
d_inferOutAt_2278 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  T_InferElabResult_82
d_inferOutAt_2278 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferOutAt_2278 v0 v1 v3 v4 v5 v6 v7 v8
du_inferOutAt_2278 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  T_InferElabResult_82
du_inferOutAt_2278 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'at_268
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
               -> coe
                    du_inferOutGo_2208 (coe v0) (coe v1) (coe v10) (coe v11) (coe v3)
                    (coe v4) (coe v5) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'other_272
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("Out" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutOn
d_inferOutOn_2314 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferOutOn_2314 v0 v1 ~v2 v3 = du_inferOutOn_2314 v0 v1 v3
du_inferOutOn_2314 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferOutOn_2314 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_inferOutAt_2278 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
             (coe MAlonzo.Code.Once.TypeCheck.TargetView.du_nuView_278 (coe v3))
      C_failure_100 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstAt
d_inferFstAt_2352 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
d_inferFstAt_2352 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferFstAt_2352 v1 v3 v4 v5 v6 v7 v8
du_inferFstAt_2352 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
du_inferFstAt_2352 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_328
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> coe
                    C_success_98 (coe v9)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v2 v1
                       (coe MAlonzo.Code.Once.IR.C_fst_42) v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstOn
d_inferFstOn_2388 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferFstOn_2388 ~v0 v1 ~v2 v3 = du_inferFstOn_2388 v1 v3
du_inferFstOn_2388 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferFstOn_2388 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferFstAt_2352 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndAt
d_inferSndAt_2426 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
d_inferSndAt_2426 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferSndAt_2426 v1 v3 v4 v5 v6 v7 v8
du_inferSndAt_2426 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
du_inferSndAt_2426 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'at_328
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> coe
                    C_success_98 (coe v10)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v2 v1
                       (coe MAlonzo.Code.Once.IR.C_snd_48) v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndOn
d_inferSndOn_2462 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferSndOn_2462 ~v0 v1 ~v2 v3 = du_inferSndOn_2462 v1 v3
du_inferSndOn_2462 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferSndOn_2462 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferSndAt_2426 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyAt
d_inferApplyAt_2500 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  T_InferElabResult_82
d_inferApplyAt_2500 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferApplyAt_2500 v0 v1 v3 v4 v5 v6 v7 v8
du_inferApplyAt_2500 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  T_InferElabResult_82
du_inferApplyAt_2500 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'at_298
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                      -> case coe v15 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Once.Spec.Grade.C_fin_42 v19
                                    -> case coe v19 of
                                         MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                           -> let v20
                                                    = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                        (coe v0) (coe v14) (coe v13) in
                                              coe
                                                (case coe v20 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> if coe v21
                                                          then coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    C_success_98 (coe v16)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                             (coe v1)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                          (coe v3)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                       v3
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
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
                                                                       v4)
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v5))
                                                                    (coe v6))
                                                          else coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    C_failure_100
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                       (coe
                                                                          ("apply"
                                                                           ::
                                                                           Data.Text.Text))))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                           -> let v20
                                                    = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                        (coe v0) (coe v14) (coe v13) in
                                              coe
                                                (case coe v20 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                     -> if coe v21
                                                          then coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    C_success_98
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                          (coe v18))
                                                                       (coe v16))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                             (coe v1)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                          (coe v3)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                       v3
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
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
                                                                                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                      (coe v0)
                                                                                      (coe v14))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                      (coe v0)
                                                                                      (coe v16)))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                                   (coe v0)
                                                                                   (coe v14)))
                                                                             (coe
                                                                                MAlonzo.Code.Once.IR.C_apply_90)
                                                                             (coe
                                                                                MAlonzo.Code.Once.IR.C_fst_42)))
                                                                       v4)
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v5))
                                                                    (coe v6))
                                                          else coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    C_failure_100
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                       (coe
                                                                          ("apply"
                                                                           ::
                                                                           Data.Text.Text))))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                    -> let v19
                                             = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                 (coe v0) (coe v14) (coe v13) in
                                       coe
                                         (case coe v19 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                              -> if coe v20
                                                   then coe
                                                          seq (coe v21)
                                                          (coe
                                                             C_success_98
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                   (coe
                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                   (coe v18))
                                                                (coe v16))
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                      (coe v1)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                   (coe
                                                                      MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                                   (coe v3)))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                v3
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
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
                                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                               (coe v0) (coe v14))
                                                                            (coe
                                                                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                               (coe v0) (coe v16)))
                                                                         (coe
                                                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                                            (coe v0) (coe v14)))
                                                                      (coe
                                                                         MAlonzo.Code.Once.IR.C_apply_90)
                                                                      (coe
                                                                         MAlonzo.Code.Once.IR.C_fst_42)))
                                                                v4)
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v5))
                                                             (coe v6))
                                                   else coe
                                                          seq (coe v21)
                                                          (coe
                                                             C_failure_100
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                (coe ("apply" :: Data.Text.Text))))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_apply'45'other_302
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("apply" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyOn
d_inferApplyOn_2694 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferApplyOn_2694 v0 v1 ~v2 v3 = du_inferApplyOn_2694 v0 v1 v3
du_inferApplyOn_2694 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferApplyOn_2694 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_inferApplyAt_2500 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_applyView_308 (coe v3))
      C_failure_100 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_2724 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RPair'45'aux_2724 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RPair'45'aux_2724 v4 v5
du_inferElabV'45'RPair'45'aux_2724 ::
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RPair'45'aux_2724 v0 v1
  = case coe v0 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v1 of
             C_success_98 v7 v8 v9 v10 v11
               -> coe
                    C_success_98
                    (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v3)
                       (coe v8))
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v3 v8 v4 v9)
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v10))
                    (coe v11)
             C_failure_100 v7 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RAnnot-aux
d_inferElabV'45'RAnnot'45'aux_2776 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
d_inferElabV'45'RAnnot'45'aux_2776 v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_2776 v0 v3 v4
du_inferElabV'45'RAnnot'45'aux_2776 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
du_inferElabV'45'RAnnot'45'aux_2776 v0 v1 v2
  = case coe v2 of
      C_success_126 v3 v4 v5 v6
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v1))
             (coe v3) (coe v4) (coe v5) (coe v6)
      C_failure_128 v3 -> coe C_failure_100 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-aux
d_inferElabV'45'RNeg'45'aux_2806 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RNeg'45'aux_2806 v0 ~v1 ~v2 v3
  = du_inferElabV'45'RNeg'45'aux_2806 v0 v3
du_inferElabV'45'RNeg'45'aux_2806 ::
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RNeg'45'aux_2806 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_success_98 (coe v2) (coe v3)
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_2892 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'neg'45'int'45'aux_2892 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) v7
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v2)))
                              (coe (2 :: Integer)) (coe (0 :: Integer))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                             (coe v3) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_2930 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'neg'45'float'45'aux_2930 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                         -> coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) v9
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                    (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                                       (coe
                                          MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                          (coe v2) (coe v3) (coe v4)))))
                              (coe (1 :: Integer)) (coe (0 :: Integer))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v8)
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                             (coe v5) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_2978 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RBinOp'45'aux_2978 v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_inferElabV'45'RBinOp'45'aux_2978 v0 v2 v5 v6
du_inferElabV'45'RBinOp'45'aux_2978 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RBinOp'45'aux_2978 v0 v1 v2 v3
  = case coe v2 of
      C_success_98 v4 v5 v6 v7 v8
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                          (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                          (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                          (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                          (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v4)))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> case coe v3 of
                    C_success_98 v9 v10 v11 v12 v13
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v14
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                        (coe (0 :: Integer)) (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Void_20
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                        (coe (0 :: Integer)) (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v14
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Int_32
                             -> case coe v1 of
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_add_212 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_div_290 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_le_328 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                    -> coe
                                         C_success_98
                                         (coe
                                            MAlonzo.Code.Once.Spec.Type.C__'43'__24
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v5 v10 v6 v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> case coe v1 of
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v5 v10
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v6) v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v5 v10
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v6) v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v5 v10
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v6) v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v5 v10
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v6) v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_failure_100 v9
                      -> coe
                           C_failure_100
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88 (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> case coe v3 of
                    C_success_98 v9 v10 v11 v12 v13
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v14
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                        (coe (0 :: Integer)) (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Void_20
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                        (coe (0 :: Integer)) (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v14
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v14 v15
                             -> coe
                                  C_failure_100
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                                        (coe v4) (coe v9)))
                           MAlonzo.Code.Once.Spec.Type.C_Int_32
                             -> case coe v1 of
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                    -> coe
                                         C_success_98 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v5 v10 v6
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v11))
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                    -> coe
                                         C_success_98 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v5 v10 v6
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v11))
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                    -> coe
                                         C_success_98 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v5 v10 v6
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v11))
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                    -> coe
                                         C_success_98 (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v5 v10 v6
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v11))
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer)) (coe v4) (coe v9)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> case coe v1 of
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpAdd_46
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpSub_48
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMul_50
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpDiv_52
                                    -> coe
                                         C_success_98 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                            (coe v5) (coe v10))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v5 v10 v6
                                            v11)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                            (coe v12))
                                         (coe v13)
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpMod_54
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLt_56
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpLe_58
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGt_60
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpGe_62
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpEq_64
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  MAlonzo.Code.Once.Spec.Surface.Syntax.C_OpNe_66
                                    -> coe
                                         C_failure_100
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v9)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_failure_100 v9
                      -> coe
                           C_failure_100
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_88 (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v4
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_86 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_3920 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux2_3920 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
                                  ~v9 v10
  = du_inferElabV'45'RLet'45'aux2_3920 v5 v6 v7 v8 v10
du_inferElabV'45'RLet'45'aux2_3920 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux2_3920 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v12
               -> coe
                    C_success_98 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v12)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v11)
                          (coe v1)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v1 v12 v11 v0 v2 v7)
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v8)))
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-join
d_inferElabV'45'RDestruct'45'join_4010 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'join_4010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                       v23
  = du_inferElabV'45'RDestruct'45'join_4010
      v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_inferElabV'45'RDestruct'45'join_4010 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'join_4010 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16
  = case coe v16 of
      MAlonzo.Code.Once.Type.Join.C_joined_174 v17 v18
        -> coe
             C_success_98 (coe v17)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
                (coe
                   MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v7) (coe v12)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v2 v7 v12 v6 v11 v0
                v1 v3
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v5
                   (coe
                      MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''8658''60''58'_62
                      (coe v5) (coe v17)
                      (coe
                         MAlonzo.Code.Once.Spec.Sub.d_left_166
                         (coe
                            MAlonzo.Code.Once.Type.Join.du_sound_714 (coe v5) (coe v10)
                            (coe v17) (coe v18))))
                   v8)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10
                   (coe
                      MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''8658''60''58'_62
                      (coe v10) (coe v17)
                      (coe
                         MAlonzo.Code.Once.Spec.Sub.d_right_168
                         (coe
                            MAlonzo.Code.Once.Type.Join.du_sound_714 (coe v5) (coe v10)
                            (coe v17) (coe v18))))
                   v13))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v4)
                   (coe addInt (coe (1 :: Integer)) (coe v9)))
                (coe addInt (coe (1 :: Integer)) (coe v14)))
             (coe v15)
      MAlonzo.Code.Once.Type.Join.C_apart_176
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_48)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-case-join
d_given'45'case'45'join_4108 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_GivenElabResult_172
d_given'45'case'45'join_4108 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16
  = du_given'45'case'45'join_4108
      v0 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_given'45'case'45'join_4108 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_GivenElabResult_172
du_given'45'case'45'join_4108 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.Type.Join.C_joined_174 v14 v15
        -> coe
             C_success_192 (coe v14)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v5)
                (coe v9))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v5 v9
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                      (coe v4))
                   (coe
                      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                      (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v1))
                      (coe
                         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''8658''60''58'_62
                         (coe v4) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Spec.Sub.d_left_166
                            (coe
                               MAlonzo.Code.Once.Type.Join.du_sound_714 (coe v4) (coe v8)
                               (coe v14) (coe v15))))
                      (MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_12 (coe v3)))
                   v6)
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                   (coe
                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v2)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                      (coe v8))
                   (coe
                      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                      (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v2))
                      (coe
                         MAlonzo.Code.Once.Type.Sub.du_'60''58''7580''8658''60''58'_62
                         (coe v8) (coe v14)
                         (coe
                            MAlonzo.Code.Once.Spec.Sub.d_right_168
                            (coe
                               MAlonzo.Code.Once.Type.Join.du_sound_714 (coe v4) (coe v8)
                               (coe v14) (coe v15))))
                      (MAlonzo.Code.Once.Type.Sub.d_'8849'π'45'refl_12 (coe v3)))
                   v10))
             (coe
                addInt (coe (1 :: Integer))
                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v11)))
             (coe v12)
      MAlonzo.Code.Once.Type.Join.C_apart_176
        -> coe
             C_failure_194
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_4200 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'auxR_4200 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 ~v12 v13 v14 v15 v16 v17 ~v18 v19
  = du_inferElabV'45'RDestruct'45'auxR_4200
      v0 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17 v19
du_inferElabV'45'RDestruct'45'auxR_4200 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'auxR_4200 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = case coe v11 of
      C_success_98 v12 v13 v14 v15 v16
        -> case coe v13 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v18 v19
               -> coe
                    du_inferElabV'45'RDestruct'45'join_4010 (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v12) (coe v18) (coe v19) (coe v14) (coe v15) (coe v16)
                    (coe
                       MAlonzo.Code.Once.Type.Join.d_join'63'_638 (coe v0) (coe v6)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-word
d_inferElabV'45'RResolved'45'word_4282 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'word_4282 ~v0 ~v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'word_4282 v2 v3 v4
du_inferElabV'45'RResolved'45'word_4282 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) -> Bool -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'word_4282 v0 v1 v2
  = if coe v2
      then coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v0)))
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_4314 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'arrow'45'aux_4314 v0 v1 v2 ~v3 v4 v5
                                               v6 ~v7 v8 ~v9 v10 ~v11
  = du_inferElabV'45'RResolved'45'arrow'45'aux_4314
      v0 v1 v2 v4 v5 v6 v8 v10
du_inferElabV'45'RResolved'45'arrow'45'aux_4314 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'arrow'45'aux_4314 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_inferElabV'45'RResolved'45'word_4282 (coe v2)
                    (coe
                       (\ v10 ->
                          coe
                            C_success_98
                            (coe
                               MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                  (coe v4)))
                            (coe
                               MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                               (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388
                               (coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                                  (coe v4))
                               v2 (coe MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v8 v9))
                            (coe (0 :: Integer)) (coe (0 :: Integer))))
                    (coe MAlonzo.Code.Once.Name.d_wordNameB_34 (coe v2))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                       (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2))
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                          (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2))
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                   (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_4374 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'value'45'aux_4374 v0 v1 v2 ~v3 v4 ~v5
                                               v6 ~v7
  = du_inferElabV'45'RResolved'45'value'45'aux_4374 v0 v1 v2 v4 v6
du_inferElabV'45'RResolved'45'value'45'aux_4374 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'value'45'aux_4374 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_inferElabV'45'RResolved'45'word_4282 (coe v2)
             (coe
                (\ v6 ->
                   coe
                     C_success_98
                     (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v3))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                        (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                     (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v3 v2 v5)
                     (coe (0 :: Integer)) (coe (0 :: Integer))))
             (coe MAlonzo.Code.Once.Name.d_wordNameB_34 (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-def
d_inferElabV'45'RResolved'45'def_4406 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'def_4406 v0 v1 v2 ~v3
  = du_inferElabV'45'RResolved'45'def_4406 v0 v1 v2
du_inferElabV'45'RResolved'45'def_4406 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'def_4406 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v3
        -> let v4
                 = coe
                     C_failure_100
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                        (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2))) in
           coe
             (case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              du_inferElabV'45'RResolved'45'own'45'aux_4416 (coe v0) (coe v1)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v1))
                                 (coe v5))
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-own-aux
d_inferElabV'45'RResolved'45'own'45'aux_4416 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'own'45'aux_4416 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'own'45'aux_4416 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'own'45'aux_4416 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'own'45'aux_4416 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4))
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v2)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_inferElabV'45'RVar'45'poly'45'aux_2084 (coe v0) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_4426 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'aux_4426 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'aux_4426 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'aux_4426 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'aux_4426 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_4374 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_4314 (coe v0)
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
             du_inferElabV'45'RResolved'45'def_4406 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_4500 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'lookup'45'aux_4500 ~v0 ~v1 v2 v3 ~v4
  = du_inferElabV'45'RVar'45'lookup'45'aux_4500 v2 v3
du_inferElabV'45'RVar'45'lookup'45'aux_4500 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'lookup'45'aux_4500 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           C_success_98 (coe v3) (coe v5)
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_568 (coe v6))
                           (coe (0 :: Integer)) (coe (0 :: Integer))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4528 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4528 v0 v1 v2
                                                         v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe C_failure_128 (coe v3)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe C_failure_128 (coe v3)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> let v9
                               = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                   (coe v0) (coe v4) (coe v6) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> if coe v10
                                     then coe
                                            seq (coe v11)
                                            (coe
                                               du_withUnit_352
                                               (coe
                                                  C_failure_128
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe v8)
                                               (coe
                                                  (\ v12 ->
                                                     coe
                                                       C_success_126
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                             (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                          (coe MAlonzo.Code.Once.IR.C_id_20))
                                                       (coe (0 :: Integer)) (coe (0 :: Integer)))))
                                     else coe
                                            seq (coe v11)
                                            (coe
                                               C_failure_128
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                  (coe ("id" :: Data.Text.Text))))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4620 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4620 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v11
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                          (coe v0) (coe v7) (coe v6) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_352
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe v10)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              C_success_126
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_fst_42))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("fst" :: Data.Text.Text))))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe C_failure_128 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4756 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4756 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v9 v10
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> let v11
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                          (coe v0) (coe v8) (coe v6) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_352
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe v10)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              C_success_126
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_snd_48))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("snd" :: Data.Text.Text))))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe C_failure_128 (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892 ~v0
                                                               v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892 v0
                                                                v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe seq (coe v5) (coe C_failure_128 (coe v2))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe seq (coe v5) (coe C_failure_128 (coe v2))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v5 of
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18
                             -> coe
                                  du_withUnit_352
                                  (coe
                                     C_failure_128
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                        (coe ("terminal" :: Data.Text.Text))))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          C_success_126
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                             (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                          (coe (0 :: Integer)) (coe (0 :: Integer))))
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v8
                             -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
                             -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v8 v9
                             -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
                             -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v8 -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v8 v9
                             -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe C_failure_128 (coe v2)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996 ~v0
                                                              v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8 -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe C_failure_128 (coe v2)
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> coe
                                  du_withUnit_352
                                  (coe
                                     C_failure_128
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                        (coe ("initial" :: Data.Text.Text))))
                                  (coe v7)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          C_success_126
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                             (coe MAlonzo.Code.Once.IR.C_initial_76))
                                          (coe (0 :: Integer)) (coe (0 :: Integer))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6 -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v2)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe C_failure_128 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5100 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5100 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe seq (coe v6) (coe C_failure_128 (coe v3))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe seq (coe v6) (coe C_failure_128 (coe v3))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                             -> let v11
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                          (coe v0) (coe v4) (coe v9) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_352
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe v8)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              C_success_126
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_inl_54))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("inl" :: Data.Text.Text))))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v9
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v9 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe C_failure_128 (coe v3)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5236 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5236 v0 v1 v2
                                                          v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v4
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe seq (coe v6) (coe C_failure_128 (coe v3))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe seq (coe v6) (coe C_failure_128 (coe v3))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
                             -> let v11
                                      = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                          (coe v0) (coe v4) (coe v10) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                       -> if coe v12
                                            then coe
                                                   seq (coe v13)
                                                   (coe
                                                      du_withUnit_352
                                                      (coe
                                                         C_failure_128
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe v8)
                                                      (coe
                                                         (\ v14 ->
                                                            coe
                                                              C_success_126
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_inr_60))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe
                                                   seq (coe v13)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("inr" :: Data.Text.Text))))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Spec.Type.C_var_16 v9
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_μ_28 v9 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                             -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
                           MAlonzo.Code.Once.Spec.Type.C_Float_34
                             -> coe C_failure_128 (coe v3)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v4 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
        -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_failure_128 (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5370 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5370 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4528 (coe v0)
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5390 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5390 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_4620 (coe v0)
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5410 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5410 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4756 (coe v0)
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5430 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5430 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4892
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5450 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5450 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4996
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5470 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5470 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_5100 (coe v0)
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5490 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5490 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_572 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_5236 (coe v0)
             (coe v1) (coe v2) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_5510 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'dispatch_5510 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("id" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("fst" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("snd" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("terminal" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("initial" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("inl" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                (coe ("inr" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_660 v5
        -> coe
             du_inferElabV'45'RResolved'45'aux_4426 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-other
d_checkElabV'45'RResolved'45'other_5556 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RResolved'45'other_5556 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> coe du_embedOrSubsume_572 (coe v0) (coe v3) (coe v4)
      C_failure_100 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v6
               -> case coe v6 of
                    [] -> coe C_failure_128 (coe v5)
                    (:) v7 v8
                      -> case coe v8 of
                           []
                             -> coe
                                  du_checkElabV'45'RVar'45'poly'45'check'45'aux_1956 (coe v0)
                                  (coe v1) (coe v7) (coe v3) (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                                     (coe v7))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v1))
                                     (coe v7))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Scope.d_lookupPolyPrefix_74
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v1))
                                     (coe v7))
                           (:) v9 v10 -> coe C_failure_128 (coe v5)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_5594 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RResolved'45'dispatch_5594 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_5370 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_5390 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_5410 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_5430 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_5450 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_5470 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_5490 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe du_embedOrSubsume_572 (coe v0) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_660 v7
        -> coe
             d_checkElabV'45'RResolved'45'other_5556 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 v0 ~v1 ~v2 v3 v4
  = du_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 v0 v3 v4
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 v0 v1 v2
  = coe du_embedOrSubsume_572 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_5686 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'RFloat'45'aux_5686 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
              (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                         -> coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) v9
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                    (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                                       (coe v2) (coe v3) (coe v4))))
                              (coe (0 :: Integer)) (coe (0 :: Integer))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v8)
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                             (coe v5) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_5734 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer -> Integer -> Integer -> T_InferElabResult_82
d_inferElabV'45'RFloat'45'aux_5734 v0 v1 v2 v3
  = coe
      C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe
         MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
         (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_float_202
         (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
            (coe v1) (coe v2) (coe v3)))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.TypeCheck.Elaborate.checkPairOn
d_checkPairOn_5754 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_146 ->
  T_CheckElabResult_110
d_checkPairOn_5754 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_158
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
                             -> let v17
                                      = d_checkElab_6032
                                          (coe v0) (coe v1) (coe v2)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v14))
                                             (coe v15)) in
                                coe
                                  (case coe v17 of
                                     C_success_126 v18 v19 v20 v21
                                       -> let v22
                                                = d_checkElab_6032
                                                    (coe v0) (coe v1) (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                       (coe v10)
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v14))
                                                       (coe v16)) in
                                          coe
                                            (case coe v22 of
                                               C_success_126 v23 v24 v25 v26
                                                 -> coe
                                                      C_success_126
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                         (coe v18) (coe v23))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_fork''_492
                                                         v18 v23 v19 v24)
                                                      (coe
                                                         addInt (coe (1 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                            (coe v20) (coe v25)))
                                                      (coe v26)
                                               C_failure_128 v23 -> coe v22
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_128 v18 -> coe v17
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'other_162
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("pair" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_5768 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkPairLit_5768 v0 v1 v2 v3 v4 v5
  = let v6 = d_checkElab_6032 (coe v0) (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v6 of
         C_success_126 v7 v8 v9 v10
           -> let v11
                    = d_checkElab_6032 (coe v0) (coe v1) (coe v3) (coe v5) in
              coe
                (case coe v11 of
                   C_success_126 v12 v13 v14 v15
                     -> coe
                          C_success_126
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v7)
                             (coe v12))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v7 v12 v8 v13)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9) (coe v14))
                          (coe v15)
                   C_failure_128 v12 -> coe v11
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_128 v7 -> coe v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCaseOn
d_checkCaseOn_5780 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_180 ->
  T_CheckElabResult_110
d_checkCaseOn_5780 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_192
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                             -> coe
                                  d_checkCaseGo_5798 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                                  (coe v14) (coe v12) (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'other_196
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("case" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_5798 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_CheckElabResult_110
d_checkCaseGo_5798 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_checkElab_6032
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                 (coe
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                 (coe v6)) in
    coe
      (case coe v8 of
         C_success_126 v9 v10 v11 v12
           -> let v13
                    = d_checkElab_6032
                        (coe v0) (coe v1) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v5)
                           (coe
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                           (coe v6)) in
              coe
                (case coe v13 of
                   C_success_126 v14 v15 v16 v17
                     -> coe
                          C_success_126
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                             (coe v14))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v9 v14 v10 v15)
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11) (coe v16)))
                          (coe v12)
                   C_failure_128 v14 -> coe v13
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_128 v9 -> coe v8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkComposeOn
d_checkComposeOn_5810 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_214 ->
  T_CheckElabResult_110
d_checkComposeOn_5810 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_224
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           d_checkCompose'45'g_5852 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v9) (coe v11) (coe v13)
                           (coe
                              d_elabGiven_5822 (coe v0) (coe v1) (coe v3) (coe v9) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_228
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("compose" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.elabGiven
d_elabGiven_5822 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_GivenElabResult_172
d_elabGiven_5822 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_given'45'infer_296 (coe v0) (coe v3) (coe v4)
              (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v6
           -> coe
                d_elabGivenLeaf_2104 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v2))
                (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v6 v7
           -> coe
                d_elabGivenApp_5836 (coe v0) (coe v1) (coe v6) (coe v7) (coe v3)
                (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v6))
                (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v6 v7
           -> let v8
                    = d_inferElab_6022
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                           (coe v6) (coe v3))
                        (coe v7) in
              coe
                (case coe v8 of
                   C_success_98 v9 v10 v11 v12 v13
                     -> case coe v10 of
                          MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v15 v16
                            -> let v17
                                     = d_decideLeq_1222
                                         (coe v15) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) in
                               coe
                                 (case coe v17 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                      -> coe
                                           du_withUnit_352
                                           (coe
                                              C_failure_194
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                 (coe ("lambda" :: Data.Text.Text))))
                                           (coe v4)
                                           (coe
                                              (\ v19 ->
                                                 coe
                                                   C_success_192 (coe v9) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v15
                                                      v11)
                                                   (coe addInt (coe (1 :: Integer)) (coe v12))
                                                   (coe v13)))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           C_failure_194
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                              (coe v6) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v15))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_failure_100 v9 -> coe C_failure_194 (coe v9)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.elabGivenApp
d_elabGivenApp_5836 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82 -> T_GivenElabResult_172
d_elabGivenApp_5836 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe du_given'45'infer_296 (coe v0) (coe v4) (coe v5) (coe v7) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
           -> let v9
                    = coe
                        C_failure_194
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                           (coe ("cata" :: Data.Text.Text))) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Once.Spec.Type.C_μ_28 v10
                     -> let v11
                              = coe
                                  MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                  (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                                  (coe v10) in
                        coe
                          (case coe v11 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                               -> coe
                                    du_given'45'cata_466 (coe v0) (coe v1) (coe v10) (coe v5)
                                    (coe v12) (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    C_failure_194
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                       (coe ("cata" :: Data.Text.Text)))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v9)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = d_elabGiven_5822 (coe v0) (coe v1) (coe v11) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          C_success_192 v13 v14 v15 v16 v17
                            -> let v18
                                     = d_elabGiven_5822
                                         (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                               coe
                                 (case coe v18 of
                                    C_success_192 v19 v20 v21 v22 v23
                                      -> coe
                                           C_success_192
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v13)
                                              (coe v19))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v14) (coe v20))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v14 v20
                                              v15 v21)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16)
                                                 (coe v22)))
                                           (coe v23)
                                    C_failure_194 v19 -> coe v18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failure_194 v13 -> coe v12
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = d_elabGiven_5822 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          C_success_192 v13 v14 v15 v16 v17
                            -> let v18
                                     = d_elabGiven_5822
                                         (coe v0) (coe v1) (coe v11) (coe v13) (coe v5) in
                               coe
                                 (case coe v18 of
                                    C_success_192 v19 v20 v21 v22 v23
                                      -> coe
                                           C_success_192 (coe v19)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v20)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v14)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v20 v14
                                              v13 v21 v15)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v22)
                                                 (coe v16)))
                                           (coe v23)
                                    C_failure_194 v19 -> coe v18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failure_194 v13 -> coe v12
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v10 v11
                  -> let v12
                           = coe
                               C_failure_194
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                  (coe ("case" :: Data.Text.Text))) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                            -> let v15
                                     = d_elabGiven_5822
                                         (coe v0) (coe v1) (coe v11) (coe v13) (coe v5) in
                               coe
                                 (case coe v15 of
                                    C_success_192 v16 v17 v18 v19 v20
                                      -> let v21
                                               = d_elabGiven_5822
                                                   (coe v0) (coe v1) (coe v3) (coe v14) (coe v5) in
                                         coe
                                           (case coe v21 of
                                              C_success_192 v22 v23 v24 v25 v26
                                                -> coe
                                                     du_given'45'case'45'join_4108 (coe v0)
                                                     (coe v13) (coe v14) (coe v5) (coe v16)
                                                     (coe v17) (coe v18) (coe v19) (coe v22)
                                                     (coe v23) (coe v24) (coe v25) (coe v26)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.Join.d_join'63'_638
                                                        (coe v0) (coe v16) (coe v22))
                                              C_failure_194 v22 -> coe v21
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_194 v16 -> coe v15
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v12)
                _ -> coe v8
         _ -> coe v8)
-- Once.TypeCheck.Elaborate.checkCompose-g
d_checkCompose'45'g_5852 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_172 -> T_CheckElabResult_110
d_checkCompose'45'g_5852 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_192 v8 v9 v10 v11 v12
        -> let v13
                 = d_checkElab_6032
                     (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v8)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v6))
                        (coe v5)) in
           coe
             (case coe v13 of
                C_success_126 v14 v15 v16 v17
                  -> coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v14 v9 v8 v15 v10)
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16) (coe v11)))
                       (coe v17)
                C_failure_128 v14
                  -> coe
                       d_checkCompose'45'f_5868 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_194 v8
        -> coe
             d_checkCompose'45'f_5868 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_5868 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_CheckElabResult_110
d_checkCompose'45'f_5868 v0 v1 v2 v3 v4 v5 v6
  = let v7 = d_inferElab_6022 (coe v0) (coe v1) (coe v2) in
    coe
      (let v8
             = coe
                 C_failure_128
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84) in
       coe
         (case coe v7 of
            C_success_98 v9 v10 v11 v12 v13
              -> case coe v9 of
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
                     -> case coe v15 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                            -> case coe v17 of
                                 MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                   -> let v19
                                            = coe
                                                MAlonzo.Code.Once.Type.SubDecide.du_arr'45'aux_30
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                      erased))
                                                (coe
                                                   MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                                   (coe v0) (coe v14) (coe v14))
                                                (coe
                                                   MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                                   (coe v0) (coe v16) (coe v5))
                                                (coe
                                                   MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
                                                   (coe v18) (coe v6)) in
                                      coe
                                        (case coe v19 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                             -> if coe v20
                                                  then case coe v21 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                           -> let v23
                                                                    = d_checkElab_6032
                                                                        (coe v0) (coe v1) (coe v3)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                           (coe v4)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                              (coe v17) (coe v6))
                                                                           (coe v14)) in
                                                              coe
                                                                (case coe v23 of
                                                                   C_success_126 v24 v25 v26 v27
                                                                     -> coe
                                                                          C_success_126
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                             (coe v10)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                                (coe v17)
                                                                                (coe v24)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_456
                                                                             v10 v24 v14
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                                                v9 v22 v11)
                                                                             v25)
                                                                          (coe
                                                                             addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                (coe v12)
                                                                                (coe v26)))
                                                                          (coe v27)
                                                                   C_failure_128 v24 -> coe v23
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  else coe
                                                         seq (coe v21)
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_84))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v8
            _ -> coe v8))
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_5878 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkCurry_5878 v0 v1 v2 v3
  = coe
      d_checkCurryOn_5888 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_curryTarget_132 (coe v3))
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_5888 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_108 ->
  T_CheckElabResult_110
d_checkCurryOn_5888 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'at_122
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                                    -> let v20
                                             = d_checkElab_6032
                                                 (coe v0) (coe v1) (coe v2)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                       (coe v10) (coe v15))
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v19))
                                                    (coe v17)) in
                                       coe
                                         (case coe v20 of
                                            C_success_126 v21 v22 v23 v24
                                              -> coe
                                                   du_withUnit_352
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("curry" :: Data.Text.Text))))
                                                   (coe v14)
                                                   (coe
                                                      (\ v25 ->
                                                         coe
                                                           C_success_126 (coe v21)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_curry''_510
                                                              v22)
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v23))
                                                           (coe v24)))
                                            C_failure_128 v21 -> coe v20
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'other_126
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("curry" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_5896 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferOut_5896 v0 v1 v2
  = coe
      du_inferOutOn_2314 (coe v0) (coe v1)
      (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_5906 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkIn_5906 v0 v1 v2 v3
  = coe
      d_checkInOn_5916 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_inTarget_102 (coe v3))
-- Once.TypeCheck.Elaborate.checkInOn
d_checkInOn_5916 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_InTarget_86 ->
  T_CheckElabResult_110
d_checkInOn_5916 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'at_92
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    du_checkInGo_5928 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'other_96
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("In" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_5928 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkInGo_5928 v0 v1 v2 v3 v4 ~v5
  = du_checkInGo_5928 v0 v1 v2 v3 v4
du_checkInGo_5928 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkInGo_5928 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> let v6
                 = d_checkElab_6032
                     (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                        (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3))) in
           coe
             (case coe v6 of
                C_success_126 v7 v8 v9 v10
                  -> coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                          (coe
                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v7
                          (coe
                             MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                             (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3)))
                          (coe
                             MAlonzo.Code.Once.IR.C_In_94
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v3)
                                (coe v5)))
                          v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_128 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("In" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_5938 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkCata_5938 v0 v1 v2 v3
  = coe
      d_checkCataOn_5948 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_cataTarget_28 (coe v3))
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_5948 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_8 ->
  T_CheckElabResult_110
d_checkCataOn_5948 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_18
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                             -> coe
                                  du_checkCataGo_5964 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10)
                                  (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                                     (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'other_22
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_5964 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkCataGo_5964 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_checkCataGo_5964 v0 v1 v2 v3 v4 v5 v6
du_checkCataGo_5964 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkCataGo_5964 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = d_checkElab_6032
                     (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                        (coe
                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                           (coe v4))
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                        (coe v4)) in
           coe
             (case coe v8 of
                C_success_126 v9 v10 v11 v12
                  -> coe
                       du_withUnit_352
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                             (coe ("cata" :: Data.Text.Text))))
                       (coe v5)
                       (coe
                          (\ v13 ->
                             coe
                               C_success_126
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v9
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v7 v10)
                               (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)))
                C_failure_128 v9 -> coe v8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_5974 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkAna_5974 v0 v1 v2 v3
  = coe
      d_checkAnaOn_5984 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_anaTarget_66 (coe v3))
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_5984 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_38 ->
  T_CheckElabResult_110
d_checkAnaOn_5984 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_loop'45'at_46
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    du_checkLoop_6014
                    (coe
                       d_checkElab_6032 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v9) (coe v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'at_56 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v15 v16
                             -> coe
                                  du_checkAnaGo_6002 (coe v0) (coe v1) (coe v2) (coe v15) (coe v10)
                                  (coe v14) (coe v16)
                                  (coe
                                     MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                                     (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'other_60
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_6002 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkAnaGo_6002 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9
  = du_checkAnaGo_6002 v0 v1 v2 v3 v4 v5 v6 v8
du_checkAnaGo_6002 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkAnaGo_6002 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = d_checkElab_6032
                     (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v6)))
                        (coe
                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                           (coe v4))) in
           coe
             (case coe v9 of
                C_success_126 v10 v11 v12 v13
                  -> coe
                       du_withUnit_352
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                             (coe ("ana" :: Data.Text.Text))))
                       (coe v5)
                       (coe
                          (\ v14 ->
                             coe
                               C_success_126
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v10))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v10
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v8 v11)
                               (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)))
                C_failure_128 v10 -> coe v9
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkLoop
d_checkLoop_6014 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_CheckElabResult_110
d_checkLoop_6014 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_checkLoop_6014 v5
du_checkLoop_6014 :: T_CheckElabResult_110 -> T_CheckElabResult_110
du_checkLoop_6014 v0
  = case coe v0 of
      C_success_126 v1 v2 v3 v4
        -> coe
             C_success_126
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v1 v2)
             (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)
      C_failure_128 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_6022 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElab_6022 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_4500 (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal_256 (coe v0)
                (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v3)
                (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_5510 (coe v0) (coe v1)
             (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
        -> coe
             du_inferElabV'45'RApp'45'dispatch_6158 (coe v0) (coe v1) (coe v3)
             (coe v4)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_24)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
        -> coe
             du_inferElabV'45'RLet'45'aux_6090 (coe v0) (coe v1) (coe v3)
             (coe v5) (coe d_inferElab_6022 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
        -> coe
             du_inferElabV'45'RPair'45'aux_2724
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
        -> coe
             du_inferElabV'45'RDestruct'45'aux_6106 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v3)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_float_202
                (MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30
                   (coe v3) (coe v4) (coe v5)))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
        -> coe
             du_inferElabV'45'RAnnot'45'aux_2776 (coe v0) (coe v4)
             (coe
                d_checkElab_6032 (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
        -> coe
             du_inferElabV'45'RBinOp'45'aux_2978 (coe v0) (coe v3)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v4))
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
        -> coe
             d_inferElabV'45'neg'45'dispatch_6060 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_6032 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab_6032 v0 v1 v2 v3
  = coe du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Elaborate.checkElab-wf
d_checkElab'45'wf_6042 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab'45'wf_6042 v0 v1 ~v2 v3 v4
  = du_checkElab'45'wf_6042 v0 v1 v3 v4
du_checkElab'45'wf_6042 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_checkElab'45'wf_6042 v0 v1 v2 v3
  = let v4
          = coe
              du_embedOrSubsume_572 (coe v0) (coe v3)
              (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v5
           -> let v6
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_4500 (coe v5)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal'45'go_170 (coe v0)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1))
                           (coe v5)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_named_132 (coe v1))
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_debruijn_134 (coe v1))) in
              coe
                (case coe v6 of
                   C_success_98 v7 v8 v9 v10 v11
                     -> coe du_embedOrSubsume_572 (coe v0) (coe v3) (coe v6)
                   C_failure_100 v7
                     -> coe
                          du_checkElabV'45'RVar'45'bbc'45'other'45'aux_5664 (coe v0) (coe v3)
                          (coe v6)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v5
           -> coe
                d_checkElabV'45'RResolved'45'dispatch_5594 (coe v0) (coe v1)
                (coe v5) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692 (coe v5))
                (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v5 v6
           -> coe
                du_checkElabV'45'RApp'45'dispatch_6172 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v5 v6
           -> let v7
                    = coe
                        C_failure_128
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_26) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
                     -> case coe v9 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                            -> let v13
                                     = d_checkElab_6032
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148
                                            (coe v1) (coe v5) (coe v8))
                                         (coe v6) (coe v10) in
                               coe
                                 (case coe v13 of
                                    C_success_126 v14 v15 v16 v17
                                      -> case coe v14 of
                                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v19 v20
                                             -> let v21 = d_decideLeq_1222 (coe v19) (coe v11) in
                                                coe
                                                  (case coe v21 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                       -> coe
                                                            du_withUnit_352
                                                            (coe
                                                               C_failure_128
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                  (coe
                                                                     ("lambda" :: Data.Text.Text))))
                                                            (coe v12)
                                                            (coe
                                                               (\ v23 ->
                                                                  coe
                                                                    C_success_126 (coe v20)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lam_38
                                                                       v19 v15)
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v16))
                                                                    (coe v17)))
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_78
                                                               (coe v5) (coe v11) (coe v19))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    C_failure_128 v14 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v7)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v5 v6
           -> coe
                d_checkElabV'45'RPair'45'aux_6204 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3) (coe du_classifyRPairTarget_60 (coe v3))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v5
           -> coe
                d_checkElabV'45'RInt'45'aux_6192 (coe v0) (coe v1) (coe v5)
                (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v5 v6 v7
           -> coe
                d_checkElabV'45'RFloat'45'aux_5686 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v7) (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_6078 (coe v0) (coe v1) (coe v5)
                (coe v3) (coe d_negOperandView_150 (coe v5))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_6052 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'other_6052 v0 v1 v2 v3
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_6146 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHead_580 (coe v2))
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_6060 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElabV'45'neg'45'dispatch_6060 v0 v1 v2
  = coe
      d_inferElabV'45'neg'45'aux_6068 (coe v0) (coe v1) (coe v2)
      (coe d_negOperandView_150 (coe v2))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_6068 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_NegOperandView_130 -> T_InferElabResult_82
d_inferElabV'45'neg'45'aux_6068 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_134
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v5
               -> coe
                    C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v5))
                    (coe (2 :: Integer)) (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_142
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v7 v8 v9
               -> coe
                    C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_float_202
                       (MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                          (coe
                             MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v7)
                             (coe v8) (coe v9))))
                    (coe (1 :: Integer)) (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_146
        -> coe
             du_inferElabV'45'RNeg'45'aux_2806 (coe v0)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_6078 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_NegOperandView_130 -> T_CheckElabResult_110
d_checkElabV'45'neg'45'dispatch_6078 v0 v1 v2 v3 v4
  = case coe v4 of
      C_nov'45'int_134
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v6
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_2892 (coe v0) (coe v1) (coe v6)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_142
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v8 v9 v10
               -> coe
                    d_checkElabV'45'neg'45'float'45'aux_2930 (coe v0) (coe v1) (coe v8)
                    (coe v9) (coe v10) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_146
        -> coe
             du_embedOrSubsume_572 (coe v0) (coe v3)
             (coe
                du_inferElabV'45'RNeg'45'aux_2806 (coe v0)
                (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_6090 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux_6090 v0 v1 v2 ~v3 v4 v5
  = du_inferElabV'45'RLet'45'aux_6090 v0 v1 v2 v4 v5
du_inferElabV'45'RLet'45'aux_6090 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux_6090 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> coe
             du_inferElabV'45'RLet'45'aux2_3920 (coe v5) (coe v6) (coe v7)
             (coe v8)
             (coe
                d_inferElab_6022 (coe v0)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                   (coe v2) (coe v5))
                (coe v3))
      C_failure_100 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_6106 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'aux_6106 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RDestruct'45'aux_6106 v0 v1 v3 v4 v5 v6 v7
du_inferElabV'45'RDestruct'45'aux_6106 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'aux_6106 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_98 v7 v8 v9 v10 v11
        -> case coe v7 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v12
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    du_inferElabV'45'RDestruct'45'auxL_6134 (coe v0) (coe v1) (coe v4)
                    (coe v5) (coe v12) (coe v13) (coe v8) (coe v9) (coe v10)
                    (coe
                       d_inferElab_6022 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                          (coe v2) (coe v12))
                       (coe v3))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v12
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v12 v13
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_6134 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'auxL_6134 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
                                       v8 v9 v10 v11 ~v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_6134
      v0 v1 v5 v6 v7 v8 v9 v10 v11 v13
du_inferElabV'45'RDestruct'45'auxL_6134 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'auxL_6134 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      C_success_98 v10 v11 v12 v13 v14
        -> case coe v11 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v16 v17
               -> coe
                    du_inferElabV'45'RDestruct'45'auxR_4200 (coe v0) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v10) (coe v16) (coe v17) (coe v12)
                    (coe v13)
                    (coe
                       d_inferElab_6022 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                          (coe v2) (coe v5))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_6146 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Scope.T_PolyBuiltinApp_270 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'other'45'aux_6146 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'other'45'aux_6146 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'other'45'aux_6146 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Scope.T_PolyBuiltinApp_270 ->
  T_InferElabResult_82
du_inferElabV'45'RApp'45'other'45'aux_6146 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe
                   ("unreachable: ahv-other \8658 classifyAppHead nothing"
                    ::
                    Data.Text.Text)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v5 = d_inferElab_6022 (coe v0) (coe v1) (coe v2) in
           coe
             (case coe v5 of
                C_success_98 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v11
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Unit_18
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Void_20
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Spec.Grade.C_fin_42 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                              -> let v17
                                                       = coe
                                                           du_checkElab'45'wf_6042 (coe v0) (coe v1)
                                                           (coe v3) (coe v11) in
                                                 coe
                                                   (case coe v17 of
                                                      C_success_126 v18 v19 v20 v21
                                                        -> coe
                                                             C_success_98 (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                (coe v7)
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                   (coe v14) (coe v18)))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_app_54
                                                                v7 v18 v11 v14 v8 v19)
                                                             (coe
                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                (coe v9) (coe v20))
                                                             (coe v21)
                                                      C_failure_128 v18
                                                        -> coe C_failure_100 (coe v18)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                              -> case coe v14 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                                     -> coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                             (coe v0) (coe v6))
                                                   MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                     -> coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                             (coe v0) (coe v6))
                                                   MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                     -> let v17
                                                              = coe
                                                                  du_checkElab'45'wf_6042 (coe v0)
                                                                  (coe v1) (coe v3) (coe v11) in
                                                        coe
                                                          (case coe v17 of
                                                             C_success_126 v18 v19 v20 v21
                                                               -> coe
                                                                    C_success_98
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                       (coe v12) (coe v13))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                       (coe v7)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                          (coe v14) (coe v18)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_effApp_72
                                                                       v7 v18 v11
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                                       v8 v19)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                       (coe v9) (coe v20))
                                                                    (coe v21)
                                                             C_failure_128 v18
                                                               -> coe C_failure_100 (coe v18)
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                       -> case coe v14 of
                                            MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                              -> coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                      (coe v0) (coe v6))
                                            MAlonzo.Code.Once.Spec.Grade.C_One_10
                                              -> coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                                      (coe v0) (coe v6))
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> let v16
                                                       = coe
                                                           du_checkElab'45'wf_6042 (coe v0) (coe v1)
                                                           (coe v3) (coe v11) in
                                                 coe
                                                   (case coe v16 of
                                                      C_success_126 v17 v18 v19 v20
                                                        -> coe
                                                             C_success_98
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                                (coe v12) (coe v13))
                                                             (coe
                                                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                (coe v7)
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                   (coe v14) (coe v17)))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_effApp_72
                                                                v7 v17 v11
                                                                (coe
                                                                   MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72)
                                                                v8 v18)
                                                             (coe
                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                (coe v9) (coe v19))
                                                             (coe v20)
                                                      C_failure_128 v17
                                                        -> coe C_failure_100 (coe v17)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Int_32
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Float_34
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_70
                                 (coe (0 :: Integer)) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_100 v6
                  -> coe
                       du_inferSpine_6182 (coe v0) (coe v1) (coe v2)
                       (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_6158 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'dispatch_6158 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'dispatch_6158 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'dispatch_6158 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82
du_inferElabV'45'RApp'45'dispatch_6158 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
        -> let v5 = d_inferElab_6022 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v5 of
                C_success_98 v6 v7 v8 v9 v10
                  -> coe
                       C_success_98 (coe v6)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                          (coe
                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v7 v6
                          (coe MAlonzo.Code.Once.IR.C_id_20) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_100 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
        -> coe
             du_inferFstOn_2388 (coe v1)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
        -> coe
             du_inferSndOn_2462 (coe v1)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
        -> let v5 = d_inferElab_6022 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v5 of
                C_success_98 v6 v7 v8 v9 v10
                  -> coe
                       C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                          (coe
                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v7 v6
                          (coe MAlonzo.Code.Once.IR.C_terminal_72) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_100 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inl_314
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_28)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inr_316
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_30)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_32)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'curry_320
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("curry" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'apply_322
        -> coe
             du_inferApplyOn_2694 (coe v0) (coe v1)
             (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'In_324
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("In" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("cata" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'ana_328
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("ana" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'Out_330
        -> coe d_inferOut_5896 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("pair" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("compose" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                (coe ("case" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'other_346
        -> coe
             d_inferElabV'45'RApp'45'other_6052 (coe v0) (coe v1) (coe v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_6172 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RApp'45'dispatch_6172 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkElabV'45'RApp'45'dispatch_6172 v0 v1 v2 v3 v4 v5
du_checkElabV'45'RApp'45'dispatch_6172 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_CheckElabResult_110
du_checkElabV'45'RApp'45'dispatch_6172 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
        -> let v6 = d_inferElab_6022 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               C_success_98 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_id_20) v9)
                               (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11) in
                     coe (coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v12))
                C_failure_100 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v8 -> coe C_failure_128 (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
        -> let v6
                 = coe
                     du_inferFstOn_2388 (coe v1)
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
        -> let v6
                 = coe
                     du_inferSndOn_2462 (coe v1)
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
        -> let v6 = d_inferElab_6022 (coe v0) (coe v1) (coe v3) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                     (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_terminal_72) v9)
                               (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11) in
                     coe (coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v12))
                C_failure_100 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v8 -> coe C_failure_128 (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inl_314
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v3) (coe v6) in
                  coe
                    (case coe v8 of
                       C_success_126 v9 v10 v11 v12
                         -> coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                    (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v6
                                 (coe MAlonzo.Code.Once.IR.C_inl_54) v10)
                              (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                       C_failure_128 v9 -> coe v8
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inr_316
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v3) (coe v7) in
                  coe
                    (case coe v8 of
                       C_success_126 v9 v10 v11 v12
                         -> coe
                              C_success_126
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                    (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v7
                                 (coe MAlonzo.Code.Once.IR.C_inr_60) v10)
                              (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                       C_failure_128 v9 -> coe v8
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
        -> let v6
                 = coe
                     du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v3)
                     (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) in
           coe
             (case coe v6 of
                C_success_126 v7 v8 v9 v10
                  -> coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                          (coe
                             MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v7
                          (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                          (coe MAlonzo.Code.Once.IR.C_initial_76) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_128 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'curry_320
        -> coe d_checkCurry_5878 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'apply_322
        -> let v6
                 = coe
                     du_inferApplyOn_2694 (coe v0) (coe v1)
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'In_324
        -> coe d_checkIn_5906 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
        -> coe d_checkCata_5938 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'ana_328
        -> coe d_checkAna_5974 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'Out_330
        -> let v6
                 = coe
                     du_inferOutOn_2314 (coe v0) (coe v1)
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkPairOn_5754 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_pairTarget_168 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkComposeOn_5810 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_arrowTarget_234 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v7 v8
               -> coe
                    d_checkCaseOn_5780 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_caseTarget_202 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'other_346
        -> let v7
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_6158 (coe v0) (coe v1) (coe v2)
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                        (coe v2)) in
           coe
             (case coe v7 of
                C_success_98 v8 v9 v10 v11 v12
                  -> coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v7)
                C_failure_100 v8 -> coe C_failure_128 (coe v8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_6182 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferSpine_6182 v0 v1 v2 ~v3 ~v4 v5
  = du_inferSpine_6182 v0 v1 v2 v5
du_inferSpine_6182 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferSpine_6182 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> let v9
                 = d_elabGiven_5822
                     (coe v0) (coe v1) (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.C_fin_42
                        (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)) in
           coe
             (case coe v9 of
                C_success_192 v10 v11 v12 v13 v14
                  -> coe
                       C_success_98 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_app_54 v11 v5 v4
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v12 v6)
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v13) (coe v7)))
                       (coe v14)
                C_failure_194 v10 -> coe C_failure_100 (coe v10)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_100 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_6192 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'RInt'45'aux_6192 v0 v1 v2 v3
  = let v4
          = coe
              C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
              (coe
                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
              (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v2)
              (coe (0 :: Integer)) (coe (0 :: Integer)) in
    coe (coe du_embedOrSubsume_572 (coe v0) (coe v3) (coe v4))
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_6204 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_RPairTarget_32 -> T_CheckElabResult_110
d_checkElabV'45'RPair'45'aux_6204 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_rpt'45'prod_40
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
               -> coe
                    d_checkPairLit_5768 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_50
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> coe
                           C_failure_128
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14))
                                 (coe v12))
                              (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'other_54
        -> let v7
                 = coe
                     du_inferElabV'45'RPair'45'aux_2724
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2))
                     (coe d_inferElab_6022 (coe v0) (coe v1) (coe v3)) in
           coe (coe du_embedOrSubsume_572 (coe v0) (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_9566 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkApply_9566 v0 v1 v2 v3
  = let v4 = d_inferElab_6022 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v4 of
         C_success_98 v5 v6 v7 v8 v9
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C_var_16 v10
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Unit_18
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Void_20
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v10 v11
                  -> case coe v10 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v12
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Unit_18
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Void_20
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                         -> case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_fin_42 v17
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("apply" :: Data.Text.Text))))
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                      (coe ("apply" :: Data.Text.Text)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Spec.Grade.C_One_10
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_fin_42 v17
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                         (coe ("apply" :: Data.Text.Text))))
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                      (coe ("apply" :: Data.Text.Text)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_fin_42 v17
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                                     -> let v18
                                                              = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                                  (coe v0) (coe v12) (coe v11) in
                                                        coe
                                                          (let v19
                                                                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                                                                     (coe v0) (coe v3) (coe v14) in
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
                                                                                                  C_success_126
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                                                                           (coe
                                                                                                              v1)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                                                        (coe
                                                                                                           v15)
                                                                                                        (coe
                                                                                                           v6)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438
                                                                                                     v6
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                                                                        (coe
                                                                                                           v10)
                                                                                                        (coe
                                                                                                           v12))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.IR.C_apply_90)
                                                                                                     v7)
                                                                                                  (coe
                                                                                                     addInt
                                                                                                     (coe
                                                                                                        (1 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        v8))
                                                                                                  (coe
                                                                                                     v9))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v23)
                                                                                               (coe
                                                                                                  C_failure_128
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_64
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v3)
                                                                                                     (coe
                                                                                                        v14)))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       else coe
                                                                              seq (coe v21)
                                                                              (coe
                                                                                 C_failure_128
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                                                    (coe
                                                                                       ("apply"
                                                                                        ::
                                                                                        Data.Text.Text))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                                     -> coe
                                                          C_failure_128
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                             (coe ("apply" :: Data.Text.Text)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                                      (coe ("apply" :: Data.Text.Text)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v12
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Int_32
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Float_34
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                                 (coe ("apply" :: Data.Text.Text)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v10 v11
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_μ_28 v10
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Int_32
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Float_34
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_82
                          (coe ("apply" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError
         C_failure_100 v5 -> coe C_failure_128 (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_9826 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_InferElabResult_82
d_inferElab'45'RApp'45'other_9826 v0 v1 v2 v3
  = let v4
          = coe
              du_asFun_1042 (coe v0)
              (coe d_inferElab_6022 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v4 of
         C_isFun_1020 v5 v6 v7 v8 v9 v10 v11
           -> let v12
                    = coe
                        du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v3) (coe v5) in
              coe
                (case coe v12 of
                   C_success_126 v13 v14 v15 v16
                     -> coe
                          C_success_98 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v6)
                                (coe v13)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_app_54 v8 v13 v5 v6 v9 v14)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10) (coe v15))
                          (coe v16)
                   C_failure_128 v13 -> coe C_failure_100 (coe v13)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_isEff_1032 v5 v6 v7 v8 v9 v10 v11 v12
           -> let v13
                    = coe
                        du_checkElab'45'wf_6042 (coe v0) (coe v1) (coe v3) (coe v7) in
              coe
                (case coe v13 of
                   C_success_126 v14 v15 v16 v17
                     -> coe
                          C_success_98
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                             (coe v8))
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v14)))
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v14 v7 v6 v10 v15)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11) (coe v16))
                          (coe v17)
                   C_failure_128 v14 -> coe C_failure_100 (coe v14)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_notFun_1034 v5 -> coe C_failure_100 (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
