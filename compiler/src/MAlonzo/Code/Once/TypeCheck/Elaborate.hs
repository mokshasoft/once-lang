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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Generators
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Generators
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Map
import qualified MAlonzo.Code.Once.Surface.Numeric
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Concrete
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Determined
import qualified MAlonzo.Code.Once.Type.Join
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.MatchCorrect
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.Type.SubDecide
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.NumTable
import qualified MAlonzo.Code.Once.TypeCheck.Scope
import qualified MAlonzo.Code.Once.TypeCheck.Table
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
    C_failure_100 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_110 a0 a1 a2 a3 = ()
data T_CheckElabResult_110
  = C_success_126 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_128 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.GivenElabResult
d_GivenElabResult_140 a0 a1 a2 a3 a4 = ()
data T_GivenElabResult_140
  = C_success_160 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                  MAlonzo.Code.Once.Spec.Context.T_Usage_34
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_failure_162 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.given-infer-dec
d_given'45'infer'45'dec_188 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  T_GivenElabResult_140
d_given'45'infer'45'dec_188 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13
  = du_given'45'infer'45'dec_188
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_given'45'infer'45'dec_188 ::
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
  T_GivenElabResult_140
du_given'45'infer'45'dec_188 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
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
                                                C_success_160 (coe v3) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
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
                                            C_failure_162
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
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
                       C_failure_162
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
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
d_given'45'infer_264 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_given'45'infer_264 v0 ~v1 ~v2 v3 v4 v5
  = du_given'45'infer_264 v0 v3 v4 v5
du_given'45'infer_264 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
du_given'45'infer_264 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> let v9
                 = coe
                     C_failure_162
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_96) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
                  -> case coe v11 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                         -> case coe v13 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     du_given'45'infer'45'dec_188 (coe v0) (coe v1) (coe v10)
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
      C_failure_100 v4 -> coe C_failure_162 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.withUnit
d_withUnit_320 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit_320 ~v0 v1 v2 v3 = du_withUnit_320 v1 v2 v3
du_withUnit_320 ::
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit_320 v0 v1 v2
  = coe
      du_withUnit'45'aux_326 (coe v0)
      (coe
         MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (coe v1))
      (coe v2)
-- Once.TypeCheck.Elaborate.withUnit-aux
d_withUnit'45'aux_326 ::
  () ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'aux_326 ~v0 ~v1 v2 v3 v4
  = du_withUnit'45'aux_326 v2 v3 v4
du_withUnit'45'aux_326 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'aux_326 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v2 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v4) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata-dec
d_given'45'cata'45'dec_370 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  T_GivenElabResult_140
d_given'45'cata'45'dec_370 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10
                           v11 v12 v13
  = du_given'45'cata'45'dec_370 v1 v4 v5 v7 v9 v10 v11 v12 v13
du_given'45'cata'45'dec_370 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
du_given'45'cata'45'dec_370 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       du_withUnit_320
                       (coe
                          C_failure_162
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                             (coe ("cata" :: Data.Text.Text))))
                       (coe v1)
                       (coe
                          (\ v11 ->
                             coe
                               C_success_160 (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v4
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v0)) v2 v5)
                               (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))))
             else coe
                    seq (coe v10)
                    (coe
                       C_failure_162
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("cata" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-cata
d_given'45'cata_434 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_given'45'cata_434 v0 v1 ~v2 v3 v4 v5 v6
  = du_given'45'cata_434 v0 v1 v3 v4 v5 v6
du_given'45'cata_434 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
du_given'45'cata_434 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_98 v6 v7 v8 v9 v10
        -> let v11
                 = coe
                     C_failure_162
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                        (coe ("cata" :: Data.Text.Text))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
                  -> coe
                       du_given'45'cata'45'dec_370 (coe v1) (coe v3) (coe v4) (coe v14)
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
      C_failure_100 v6 -> coe C_failure_162 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume-dec
d_embedOrSubsume'45'dec_500 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_embedOrSubsume'45'dec_500 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'dec_500 v0 v3 v4 v5 v6 v7 v8 v9
du_embedOrSubsume'45'dec_500 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
du_embedOrSubsume'45'dec_500 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           C_success_126 (coe v1)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v3 v10 v4)
                           (coe v5) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                          (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_540 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_embedOrSubsume_540 v0 ~v1 ~v2 v3 v4
  = du_embedOrSubsume_540 v0 v3 v4
du_embedOrSubsume_540 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
du_embedOrSubsume_540 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_embedOrSubsume'45'dec_500 (coe v0) (coe v4) (coe v1) (coe v3)
             (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170 (coe v0)
                (coe v3) (coe v1))
      C_failure_100 v3 -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_572 a0 a1 a2 = ()
data T_WellFormedFView_572
  = C_wfv'45'yes_582 MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_wfv'45'no_584
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_592 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_572
d_inspectWellFormedF_592 ~v0 v1 v2
  = du_inspectWellFormedF_592 v1 v2
du_inspectWellFormedF_592 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_572
du_inspectWellFormedF_592 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468 (coe v0)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_wfv'45'yes_582 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_584
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.matchInferResult
d_matchInferResult_622 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_matchInferResult_622 v0 ~v1 ~v2 v3 v4
  = du_matchInferResult_622 v0 v3 v4
du_matchInferResult_622 ::
  Integer ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_matchInferResult_622 v0 v1 v2
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
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                                    (coe v2) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_100 v3 -> coe C_failure_128 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_672 a0 a1 a2 = ()
data T_FunProjection_672
  = C_isFun_688 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_isEff_700 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notFun_702 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.asFun
d_asFun_710 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_FunProjection_672
d_asFun_710 v0 ~v1 ~v2 v3 = du_asFun_710 v0 v3
du_asFun_710 ::
  Integer -> T_InferElabResult_82 -> T_FunProjection_672
du_asFun_710 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                    -> coe
                                         C_isFun_688 (coe v7) (coe v10) (coe v9) (coe v3) (coe v4)
                                         (coe v5) (coe v6)
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_notFun_702
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_notFun_702
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_isEff_700 (coe v11)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                (coe v7) (coe v9) (coe v3) (coe v4) (coe v5)
                                                (coe v6)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         C_notFun_702
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         C_notFun_702
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         C_isEff_700 (coe v11)
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) (coe v7)
                                         (coe v9) (coe v3) (coe v4) (coe v5) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notFun_702
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notFun_702 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_800 a0 a1 a2 = ()
data T_IntProjection_800
  = C_isInt_810 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notInt_812 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.asInt
d_asInt_820 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_IntProjection_800
d_asInt_820 v0 ~v1 ~v2 v3 = du_asInt_820 v0 v3
du_asInt_820 ::
  Integer -> T_InferElabResult_82 -> T_IntProjection_800
du_asInt_820 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe C_isInt_810 (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notInt_812
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notInt_812 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.numErr
d_numErr_856 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_numErr_856 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v3
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
             (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
             (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v1))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_910 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_notNumeric_910 v0 ~v1 ~v2 v3 = du_notNumeric_910 v0 v3
du_notNumeric_910 ::
  Integer ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
du_notNumeric_910 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
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
d_decideLeq_940 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_940 v0 v1
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
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_944 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_944 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_988 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  T_GivenElabResult_140
d_given'45'poly'45'k_988 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11
                         ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20
  = du_given'45'poly'45'k_988 v0 v1 v2 v3 v4 v6 v8 v19 v20
du_given'45'poly'45'k_988 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
du_given'45'poly'45'k_988 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       C_success_160 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                             (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v3))
                             (coe MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32 (coe v4))
                             v7)
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v2))
                       (coe (0 :: Integer)) (coe (0 :: Integer)))
             else coe
                    seq (coe v10)
                    (coe
                       C_failure_162
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0) (coe v2)
                          (coe v6)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                             (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-π
d_given'45'poly'45'π_1076 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  T_GivenElabResult_140
d_given'45'poly'45'π_1076 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_given'45'poly'45'π_1076 v0 v1 v2 v3 v4 v6 v8 v9 v18 v20
du_given'45'poly'45'π_1076 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
du_given'45'poly'45'π_1076 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> if coe v10
             then case coe v11 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                      -> coe
                           du_given'45'poly'45'k_988 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe
                              MAlonzo.Code.Once.Type.Poly.d_substPoly_186 (coe v0) (coe v8)
                              (coe v6))
                           (coe v7) (coe v5) (coe v12)
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
             else coe
                    seq (coe v11)
                    (coe
                       C_failure_162
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0) (coe v2)
                          (coe v5)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                             (coe
                                MAlonzo.Code.Once.Type.Poly.d_substPoly_186 (coe v0) (coe v8)
                                (coe v6)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-m
d_given'45'poly'45'm_1168 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  T_GivenElabResult_140
d_given'45'poly'45'm_1168 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_given'45'poly'45'm_1168 v0 v1 v2 v3 v4 v6 v7 v8 v9 v18
du_given'45'poly'45'm_1168 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_GivenElabResult_140
du_given'45'poly'45'm_1168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             du_given'45'poly'45'π_1076 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Type.MatchCorrect.du_instantiate'45'sound_1850
                   (coe v0) (coe v6) (coe v3) (coe v10)))
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10 (coe v8)
                (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0) (coe v2)
                (coe v6) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-d
d_given'45'poly'45'd_1248 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Type.Poly.T_ArrowSchema_314 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
d_given'45'poly'45'd_1248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 v17
  = du_given'45'poly'45'd_1248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v17
du_given'45'poly'45'd_1248 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
du_given'45'poly'45'd_1248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then coe
                    seq (coe v12)
                    (coe
                       du_given'45'poly'45'm_1168 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.Type.Match.d_instantiate_100 (coe v0) (coe v7)
                          (coe v3)))
             else coe seq (coe v12) (coe C_failure_162 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1312 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
d_given'45'poly'45'a_1312 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 v13
  = du_given'45'poly'45'a_1312 v0 v1 v2 v3 v4 v5 v6 v13
du_given'45'poly'45'a_1312 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
du_given'45'poly'45'a_1312 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  du_given'45'poly'45'd_1248 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6) (coe v9) (coe v11) (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_608
                                     (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_failure_162 (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-g
d_given'45'poly'45'g_1378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_GivenElabResult_140
d_given'45'poly'45'g_1378 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 v12 ~v13
  = du_given'45'poly'45'g_1378 v0 v1 v2 v3 v4 v5 v6 v12
du_given'45'poly'45'g_1378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_GivenElabResult_140
du_given'45'poly'45'g_1378 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe C_failure_162 (coe v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             seq (coe v8)
             (coe
                du_given'45'poly'45'a_1312 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_626 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1436 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_GivenElabResult_140
d_given'45'poly_1436 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 v10 ~v11
  = du_given'45'poly_1436 v0 v1 v2 v3 v4 v5 v6 v8 v10
du_given'45'poly_1436 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
du_given'45'poly_1436 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe C_failure_162 (coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe C_failure_162 (coe v5)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  seq (coe v11)
                                  (coe
                                     du_given'45'poly'45'g_1378 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v10)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_162 (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-res
d_given'45'res_1500 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_given'45'res_1500 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_98 v6 v7 v8 v9 v10
        -> coe du_given'45'infer_264 (coe v0) (coe v3) (coe v4) (coe v5)
      C_failure_100 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v7
               -> case coe v7 of
                    [] -> coe C_failure_162 (coe v6)
                    (:) v8 v9
                      -> case coe v9 of
                           []
                             -> coe
                                  du_given'45'poly_1436 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
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
                           (:) v10 v11 -> coe C_failure_162 (coe v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-inst-aux
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554 v0 v1 v2 v3 ~v4 v5
                                                 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554
      v0 v1 v2 v3 v5 v12
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v2)
                       (coe (0 :: Integer)) (coe (0 :: Integer)))
             else coe
                    seq (coe v7)
                    (coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0) (coe v2)
                          (coe v4) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-ground-aux
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610 v0 v1 v2 v3 v4
                                                   v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610
      v0 v1 v2 v3 v4 v5 v11
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610 v0 v1 v2 v3 v4
                                                    v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe C_failure_128 (coe v4)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             seq (coe v7)
             (coe
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1554 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v5)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                   (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                   (coe v5) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1662 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1662 v0 v1 v2 v3 v4 v5
                                                  ~v6 v7 ~v8 v9 ~v10
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_1662
      v0 v1 v2 v3 v4 v5 v7 v9
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1662 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1662 v0 v1 v2 v3 v4
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
                                     du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1610 (coe v0)
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_128 (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6 ~v7 v8 ~v9
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720
      v0 v1 v2 v5 v8
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720 v0 v1 v2 v3 v4
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
             (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v2)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             seq (coe v5)
             (coe
                C_failure_100
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 v0 v1 v2 v5
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1720 (coe v0)
                    (coe v1) (coe v2) (coe v5)
                    (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-aux
d_inferElabV'45'RVar'45'poly'45'aux_1790 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'aux_1790 v0 v1 v2 ~v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'aux_1790 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'aux_1790 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'aux_1790 v0 v1 v2
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1760 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_10
         (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v1))
         (coe v2))
-- Once.TypeCheck.Elaborate.determinedErr
d_determinedErr_1804 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_determinedErr_1804 ~v0 ~v1 v2 v3 = du_determinedErr_1804 v2 v3
du_determinedErr_1804 ::
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
du_determinedErr_1804 v0 v1
  = case coe v0 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_failure_100 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_1816 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RPair'45'aux_1816 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RPair'45'aux_1816 v4 v5
du_inferElabV'45'RPair'45'aux_1816 ::
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RPair'45'aux_1816 v0 v1
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
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_88 v3 v8 v4 v9)
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v10))
                    (coe v11)
             C_failure_100 v7 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RAnnot-aux
d_inferElabV'45'RAnnot'45'aux_1868 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
d_inferElabV'45'RAnnot'45'aux_1868 v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_1868 v0 v3 v4
du_inferElabV'45'RAnnot'45'aux_1868 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
du_inferElabV'45'RAnnot'45'aux_1868 v0 v1 v2
  = case coe v2 of
      C_success_126 v3 v4 v5 v6
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v1))
             (coe v3) (coe v4) (coe v5) (coe v6)
      C_failure_128 v3 -> coe C_failure_100 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-has
d_inferElabV'45'RNeg'45'has_1904 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferElabV'45'RNeg'45'has_1904 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RNeg'45'has_1904 v2 v3 v4 v5 v6 v7
du_inferElabV'45'RNeg'45'has_1904 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
du_inferElabV'45'RNeg'45'has_1904 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then case coe v7 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                      -> coe
                           C_success_98
                           (coe
                              MAlonzo.Code.Once.Spec.Theory.du_'8988'_'8989''8319'_14 (coe v0))
                           (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_num_218 v0
                              (coe MAlonzo.Code.Once.Spec.Theory.C_Neg_18)
                              (coe MAlonzo.Code.Once.Spec.Theory.C_unary_32) v8
                              (coe MAlonzo.Code.Once.Spec.Theory.C_'8245'neg_40) v2)
                           (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v7)
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_OperatorUndefined_102
                          (coe ("-" :: Data.Text.Text)) (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-num
d_inferElabV'45'RNeg'45'num_1940 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
d_inferElabV'45'RNeg'45'num_1940 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RNeg'45'num_1940 v0 v2 v3 v4 v5 v6 v7
du_inferElabV'45'RNeg'45'num_1940 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
du_inferElabV'45'RNeg'45'num_1940 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v7
        -> coe
             du_inferElabV'45'RNeg'45'has_1904 (coe v7) (coe v2) (coe v3)
             (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.TypeCheck.NumTable.d_has'63'_44 (coe v7)
                (coe MAlonzo.Code.Once.Spec.Theory.C_Neg_18))
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                d_numErr_856 (coe v0) (coe MAlonzo.Code.Once.Spec.Theory.C_int_8)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-aux
d_inferElabV'45'RNeg'45'aux_1968 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RNeg'45'aux_1968 v0 ~v1 ~v2 v3
  = du_inferElabV'45'RNeg'45'aux_1968 v0 v3
du_inferElabV'45'RNeg'45'aux_1968 ::
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RNeg'45'aux_1968 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RNeg'45'num_1940 (coe v0) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-has
d_inferElabV'45'RBinOp'45'has_2006 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferElabV'45'RBinOp'45'has_2006 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = du_inferElabV'45'RBinOp'45'has_2006 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_inferElabV'45'RBinOp'45'has_2006 ::
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
du_inferElabV'45'RBinOp'45'has_2006 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then case coe v10 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                      -> coe
                           C_success_98
                           (coe
                              MAlonzo.Code.Once.Spec.Theory.du_symCod_90 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Operator.d_shape_62
                                 (coe
                                    MAlonzo.Code.Once.Spec.Surface.Operator.d_binSym_68 (coe v0))))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
                              (coe v3))
                           (coe
                              MAlonzo.Code.Once.Surface.Numeric.du_numBin_22 (coe v2) (coe v3)
                              (coe v0) (coe v1) (coe v11) (coe v4) (coe v5))
                           (coe v6) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v10)
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_OperatorUndefined_102
                          (coe MAlonzo.Code.Once.TypeCheck.Error.d_opText_8 (coe v0))
                          (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-num
d_inferElabV'45'RBinOp'45'num_2056 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferElabV'45'RBinOp'45'num_2056 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9
                                   v10 v11
  = du_inferElabV'45'RBinOp'45'num_2056 v2 v3 v5 v6 v7 v8 v9 v10 v11
du_inferElabV'45'RBinOp'45'num_2056 ::
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
du_inferElabV'45'RBinOp'45'num_2056 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       du_inferElabV'45'RBinOp'45'has_2006 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.NumTable.d_has'63'_44 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Spec.Surface.Operator.d_theory_60
                             (coe
                                MAlonzo.Code.Once.Spec.Surface.Operator.d_binSym_68 (coe v0)))))
             else coe
                    seq (coe v10)
                    (coe
                       C_failure_100
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_MixedOperands_106
                          (coe MAlonzo.Code.Once.TypeCheck.Error.d_opText_8 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-R
d_inferElabV'45'RBinOp'45'R_2106 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
d_inferElabV'45'RBinOp'45'R_2106 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11
  = du_inferElabV'45'RBinOp'45'R_2106
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_inferElabV'45'RBinOp'45'R_2106 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
du_inferElabV'45'RBinOp'45'R_2106 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v11
        -> coe
             du_inferElabV'45'RBinOp'45'num_2056 (coe v1) (coe v2) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.TypeCheck.NumTable.d__'8799''8319'__38 (coe v2)
                (coe v11))
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_110
                (coe d_numErr_856 (coe v0) (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-L
d_inferElabV'45'RBinOp'45'L_2152 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RBinOp'45'L_2152 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferElabV'45'RBinOp'45'L_2152 v0 v2 v3 v4 v5 v6 v7 v8
du_inferElabV'45'RBinOp'45'L_2152 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RBinOp'45'L_2152 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v8
        -> case coe v7 of
             C_success_98 v9 v10 v11 v12 v13
               -> coe
                    du_inferElabV'45'RBinOp'45'R_2106 (coe v0) (coe v1) (coe v8)
                    (coe v9) (coe v3) (coe v10) (coe v4) (coe v11)
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v12))
                    (coe v13)
                    (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v9))
             C_failure_100 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_110 (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_108
                (coe
                   d_numErr_856 (coe v0) (coe MAlonzo.Code.Once.Spec.Theory.C_int_8)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_2208 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RBinOp'45'aux_2208 v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_inferElabV'45'RBinOp'45'aux_2208 v0 v2 v5 v6
du_inferElabV'45'RBinOp'45'aux_2208 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RBinOp'45'aux_2208 v0 v1 v2 v3
  = case coe v2 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe
             du_inferElabV'45'RBinOp'45'L_2152 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v4))
             (coe v3)
      C_failure_100 v4
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_108 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_2260 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux2_2260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
                                  ~v9 v10
  = du_inferElabV'45'RLet'45'aux2_2260 v5 v6 v7 v8 v10
du_inferElabV'45'RLet'45'aux2_2260 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux2_2260 v0 v1 v2 v3 v4
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
                       MAlonzo.Code.Once.Surface.Syntax.C_let''_190 v1 v12 v11 v0 v2 v7)
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                       (coe addInt (coe (1 :: Integer)) (coe v8)))
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-join
d_inferElabV'45'RDestruct'45'join_2350 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
d_inferElabV'45'RDestruct'45'join_2350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                       v23
  = du_inferElabV'45'RDestruct'45'join_2350
      v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_inferElabV'45'RDestruct'45'join_2350 ::
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
du_inferElabV'45'RDestruct'45'join_2350 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                MAlonzo.Code.Once.Surface.Syntax.C_case''_158 v2 v7 v12 v6 v11 v0
                v1 v3
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v5
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
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v10
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
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_58)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-case-join
d_given'45'case'45'join_2448 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_GivenElabResult_140
d_given'45'case'45'join_2448 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16
  = du_given'45'case'45'join_2448
      v0 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_given'45'case'45'join_2448 ::
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
  MAlonzo.Code.Once.Type.Join.T_Join'63'_164 -> T_GivenElabResult_140
du_given'45'case'45'join_2448 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.Type.Join.C_joined_174 v14 v15
        -> coe
             C_success_160 (coe v14)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v5)
                (coe v9))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_copair''_324 v5 v9
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
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
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
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
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                (coe v4) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_2540 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
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
d_inferElabV'45'RDestruct'45'auxR_2540 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 ~v12 v13 v14 v15 v16 v17 ~v18 v19
  = du_inferElabV'45'RDestruct'45'auxR_2540
      v0 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17 v19
du_inferElabV'45'RDestruct'45'auxR_2540 ::
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
du_inferElabV'45'RDestruct'45'auxR_2540 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = case coe v11 of
      C_success_98 v12 v13 v14 v15 v16
        -> case coe v13 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v18 v19
               -> coe
                    du_inferElabV'45'RDestruct'45'join_2350 (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v12) (coe v18) (coe v19) (coe v14) (coe v15) (coe v16)
                    (coe
                       MAlonzo.Code.Once.Type.Join.d_join'63'_638 (coe v0) (coe v6)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-word
d_inferElabV'45'RResolved'45'word_2622 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'word_2622 ~v0 ~v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'word_2622 v2 v3 v4
du_inferElabV'45'RResolved'45'word_2622 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) -> Bool -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'word_2622 v0 v1 v2
  = if coe v2
      then coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v0)))
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_2654 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'arrow'45'aux_2654 v0 v1 v2 v3 v4 v5
                                               ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RResolved'45'arrow'45'aux_2654
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RResolved'45'arrow'45'aux_2654 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'arrow'45'aux_2654 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_inferElabV'45'RResolved'45'word_2622 (coe v2)
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
                               MAlonzo.Code.Once.Surface.Syntax.C_sigOp_238
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
                       MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_32
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
                MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_32
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2))
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v5))
                   (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_2708 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'value'45'aux_2708 v0 v1 v2 v3 ~v4 v5
                                               ~v6
  = du_inferElabV'45'RResolved'45'value'45'aux_2708 v0 v1 v2 v3 v5
du_inferElabV'45'RResolved'45'value'45'aux_2708 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'value'45'aux_2708 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_inferElabV'45'RResolved'45'word_2622 (coe v2)
             (coe
                (\ v6 ->
                   coe
                     C_success_98
                     (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v3))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                        (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                     (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_238 v3 v2 v5)
                     (coe (0 :: Integer)) (coe (0 :: Integer))))
             (coe MAlonzo.Code.Once.Name.d_wordNameB_34 (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_32
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-def
d_inferElabV'45'RResolved'45'def_2736 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'def_2736 v0 v1 v2 ~v3
  = du_inferElabV'45'RResolved'45'def_2736 v0 v1 v2
du_inferElabV'45'RResolved'45'def_2736 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'def_2736 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v3
        -> let v4
                 = coe
                     C_failure_100
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20
                        (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2))) in
           coe
             (case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              du_inferElabV'45'RResolved'45'own'45'aux_2746 (coe v0) (coe v1)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v1))
                                 (coe v5))
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-own-aux
d_inferElabV'45'RResolved'45'own'45'aux_2746 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'own'45'aux_2746 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'own'45'aux_2746 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'own'45'aux_2746 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'own'45'aux_2746 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4))
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_246 v2)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_inferElabV'45'RVar'45'poly'45'aux_1790 (coe v0) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_2756 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'aux_2756 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'aux_2756 v0 v1 v2 v3
du_inferElabV'45'RResolved'45'aux_2756 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'aux_2756 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_2708 (coe v0) (coe v1)
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
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_2654 (coe v0)
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
             du_inferElabV'45'RResolved'45'def_2736 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_2824 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'lookup'45'aux_2824 ~v0 ~v1 v2 v3 ~v4
  = du_inferElabV'45'RVar'45'lookup'45'aux_2824 v2 v3
du_inferElabV'45'RVar'45'lookup'45'aux_2824 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'lookup'45'aux_2824 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           C_success_98 (coe v3) (coe v5)
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_418 (coe v6))
                           (coe (0 :: Integer)) (coe (0 :: Integer))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-other
d_checkElabV'45'RResolved'45'other_2852 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RResolved'45'other_2852 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v4)
      C_failure_100 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v6
               -> case coe v6 of
                    [] -> coe C_failure_128 (coe v5)
                    (:) v7 v8
                      -> case coe v8 of
                           []
                             -> coe
                                  du_checkElabV'45'RVar'45'poly'45'check'45'aux_1662 (coe v0)
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
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2890 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2890 v0 ~v1 ~v2 v3 v4
  = du_checkElabV'45'RVar'45'bbc'45'other'45'aux_2890 v0 v3 v4
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_2890 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_2890 v0 v1 v2
  = coe du_embedOrSubsume_540 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_2912 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> T_InferElabResult_82
d_inferElabV'45'RFloat'45'aux_2912 v0 v1 v2 v3 v4
  = coe
      C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe
         MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
         (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_float_204
         (MAlonzo.Code.Once.Spec.Surface.Syntax.d_signedDecimal_76
            (coe v1) (coe v2) (coe v3) (coe v4)))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.TypeCheck.Elaborate._⇒ω⟨_⟩_
d__'8658'ω'10216'_'10217'__2926 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658'ω'10216'_'10217'__2926 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
      (coe v2)
-- Once.TypeCheck.Elaborate.genErr
d_genErr_2934 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_genErr_2934 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Error.C_GeneratorInInferMode_46
              (coe
                 MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v0)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_38
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_40
         MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_42
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.spineErr
d_spineErr_2938 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_spineErr_2938 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
              (coe
                 MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v0)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_52
         MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_54
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_38
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_40
         MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_42
         _ -> coe v1)
-- Once.TypeCheck.Elaborate._⇒ω_
d__'8658'ω__2942 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d__'8658'ω__2942 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
      (coe v0) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1)
-- Once.TypeCheck.Elaborate.mapDomSchema
d_mapDomSchema_2948 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_mapDomSchema_2948 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
              (coe ("a" :: Data.Text.Text)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("b" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("b" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                (coe ("b" :: Data.Text.Text))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26
           -> coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
         MAlonzo.Code.Once.Spec.Surface.Generators.C_apply_30
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
                (coe
                   d__'8658'ω__2942
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("a" :: Data.Text.Text)))
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("b" :: Data.Text.Text))))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_In_34
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                (coe ("F (Mu F)" :: Data.Text.Text))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_Out_38
           -> coe
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                (coe ("Nu F" :: Data.Text.Text))
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.mapSchema
d_mapSchema_2950 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_mapSchema_2950 v0
  = let v1
          = d__'8658'ω__2942
              (coe
                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                 (coe ("a" :: Data.Text.Text)))
              (coe
                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                 (coe ("a" :: Data.Text.Text))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14
           -> coe
                d__'8658'ω__2942 (coe d_mapDomSchema_2948 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16
           -> coe
                d__'8658'ω__2942 (coe d_mapDomSchema_2948 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("b" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_terminal_18
           -> coe
                d__'8658'ω__2942
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
                (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20)
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22
           -> coe
                d__'8658'ω__2942
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("a" :: Data.Text.Text)))
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("b" :: Data.Text.Text))))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
           -> coe
                d__'8658'ω__2942
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("b" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("a" :: Data.Text.Text)))
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                      (coe ("b" :: Data.Text.Text))))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26
           -> coe
                d__'8658'ω__2942
                (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22)
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("a" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_apply_30
           -> coe
                d__'8658'ω__2942 (coe d_mapDomSchema_2948 (coe v0))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("b" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_In_34
           -> coe
                d__'8658'ω__2942
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("F (Mu F)" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("Mu F" :: Data.Text.Text)))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_Out_38
           -> coe
                d__'8658'ω__2942
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("Nu F" :: Data.Text.Text)))
                (coe
                   MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                   (coe ("F (Nu F)" :: Data.Text.Text)))
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.inferConst
d_inferConst_2958 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_IsConstant_72 ->
  T_InferElabResult_82
d_inferConst_2958 ~v0 v1 v2 ~v3 = du_inferConst_2958 v1 v2
du_inferConst_2958 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  T_InferElabResult_82
du_inferConst_2958 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Generators.C_unit_42
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_164)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Generators.C_toFloat_44
        -> coe
             C_success_98
             (coe
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                      (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34))
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276
                (coe MAlonzo.Code.Once.Surface.Map.C_mp'45'toFloat_70))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferGen
d_inferGen_3002 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
d_inferGen_3002 ~v0 v1 v2 v3 = du_inferGen_3002 v1 v2 v3
du_inferGen_3002 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
du_inferGen_3002 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v3
        -> coe C_failure_100 (coe d_genErr_2934 (coe v1))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe du_inferConst_2958 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe C_failure_100 (coe d_genErr_2934 (coe v1))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe C_failure_100 (coe d_genErr_2934 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.givenMap
d_givenMap_3034 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
d_givenMap_3034 v0 v1 v2 v3 ~v4 v5
  = du_givenMap_3034 v0 v1 v2 v3 v5
du_givenMap_3034 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
du_givenMap_3034 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    C_success_160 (coe v6)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v7)
                    (coe (0 :: Integer)) (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2))
                (coe d_mapDomSchema_2948 (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkMapAt
d_checkMapAt_3064 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_214 ->
  T_CheckElabResult_110
d_checkMapAt_3064 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_224
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                      -> coe
                           d_checkMapAt'45'go_3078 (coe v0) (coe v1) (coe v2) (coe v8)
                           (coe v12) (coe v10)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Table.d_mapAt'63'_656 (coe v0)
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                              (coe v2) (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_228
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2))
                (coe d_mapSchema_2950 (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkMapAt-go
d_checkMapAt'45'go_3078 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
  T_CheckElabResult_110
d_checkMapAt'45'go_3078 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             C_success_126
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v7)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2))
                (coe d_mapSchema_2950 (coe v2))
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                   (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferMapSpine
d_inferMapSpine_3124 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferMapSpine_3124 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe
             du_inferMapSpine'45'go_3142 (coe v1) (coe v2) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.TypeCheck.Table.d_mapFrom'63'_316 (coe v0)
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                (coe v2) (coe v4))
      C_failure_100 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferMapSpine-go
d_inferMapSpine'45'go_3142 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
d_inferMapSpine'45'go_3142 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferMapSpine'45'go_3142 v1 v2 v3 v4 v5 v6 v7 v8
du_inferMapSpine'45'go_3142 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferMapSpine'45'go_3142 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    C_success_98 (coe v9)
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_288 v3 v2 v10 v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_failure_100 (coe d_spineErr_2938 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.givenCata
d_givenCata_3196 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_givenCata_3196 v0 v1 v2 v3 v4
  = coe
      d_givenCata'45'mu_3206 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Once.TypeCheck.Table.du_muV_276 (coe v2))
      (coe v4)
-- Once.TypeCheck.Elaborate.givenCata-mu
d_givenCata'45'mu_3206 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Table.T_MuV_260 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_givenCata'45'mu_3206 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Table.C_mu'45'at_266
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    d_givenCata'45'wf_3216 (coe v0) (coe v1) (coe v7) (coe v3)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                       (coe v7))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Table.C_mu'45'other_270
        -> coe
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.givenCata-wf
d_givenCata'45'wf_3216 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_givenCata'45'wf_3216 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v5 of
             C_success_98 v7 v8 v9 v10 v11
               -> let v12
                        = coe
                            C_failure_162
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                               (coe ("cata" :: Data.Text.Text))) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                         -> case coe v14 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                                -> case coe v16 of
                                     MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                       -> coe
                                            du_givenCata'45'alg_3238 (coe v1) (coe v6) (coe v13)
                                            (coe v15) (coe v17) (coe v8) (coe v9) (coe v10)
                                            (coe v11)
                                            (coe
                                               MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                                  (coe v2) (coe v15))
                                               (coe v13))
                                            (coe
                                               MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
                                               (coe v17) (coe v3))
                                     _ -> coe v12
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v12)
             C_failure_100 v7 -> coe C_failure_162 (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.givenCata-alg
d_givenCata'45'alg_3238 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
d_givenCata'45'alg_3238 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                        v12 v13
  = du_givenCata'45'alg_3238 v1 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_givenCata'45'alg_3238 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_GivenElabResult_140
du_givenCata'45'alg_3238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then case coe v12 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                      -> case coe v10 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                             -> if coe v14
                                  then case coe v15 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                           -> coe
                                                C_success_160 (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                   (coe v5))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v5
                                                   (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142
                                                      (coe v0))
                                                   v1
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                         (coe v2)
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                            (coe v4))
                                                         (coe v3))
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40
                                                         v13
                                                         (coe
                                                            MAlonzo.Code.Once.Type.Sub.du_'60''58''45'refl_32
                                                            (coe v3))
                                                         v16)
                                                      v6))
                                                (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v15)
                                         (coe
                                            C_failure_162
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                               (coe ("cata" :: Data.Text.Text))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v12)
                    (coe
                       C_failure_162
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("cata" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyKind
d_PolyKind_3374 = ()
data T_PolyKind_3374
  = C_not'45'poly_3376 | C_poly'45'dom_3378 | C_poly'45'other_3380
-- Once.TypeCheck.Elaborate.polyKind-c
d_polyKind'45'c_3386 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_PolyKind_3374
d_polyKind'45'c_3386 ~v0 ~v1 v2 = du_polyKind'45'c_3386 v2
du_polyKind'45'c_3386 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_PolyKind_3374
du_polyKind'45'c_3386 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe C_poly'45'dom_3378)
             else coe seq (coe v2) (coe C_poly'45'other_3380)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.polyKind-a
d_polyKind'45'a_3390 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_PolyKind_3374
d_polyKind'45'a_3390 ~v0 v1 = du_polyKind'45'a_3390 v1
du_polyKind'45'a_3390 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_PolyKind_3374
du_polyKind'45'a_3390 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           seq (coe v5)
                           (coe
                              du_polyKind'45'c_3386
                              (coe
                                 MAlonzo.Code.Once.Type.Determined.d_codVarsInDom'63'_608 (coe v2)
                                 (coe v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_poly'45'other_3380
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.polyKind-g
d_polyKind'45'g_3400 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_PolyKind_3374
d_polyKind'45'g_3400 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_not'45'poly_3376
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             seq (coe v2)
             (coe
                du_polyKind'45'a_3390
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_626 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.polyKind-own
d_polyKind'45'own_3406 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_PolyKind_3374
d_polyKind'45'own_3406 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe C_not'45'poly_3376
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe C_not'45'poly_3376
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                             -> coe
                                  seq (coe v5)
                                  (coe
                                     d_polyKind'45'g_3400 (coe v4)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v4)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_not'45'poly_3376
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.polyKind
d_polyKind_3416 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> T_PolyKind_3374
d_polyKind_3416 ~v0 v1 v2 = du_polyKind_3416 v1 v2
du_polyKind_3416 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> T_PolyKind_3374
du_polyKind_3416 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v2
        -> case coe v2 of
             [] -> coe C_not'45'poly_3376
             (:) v3 v4
               -> case coe v4 of
                    []
                      -> coe
                           d_polyKind'45'own_3406
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v0))
                              (coe v3))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v0))
                              (coe v3))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Scope.d_lookupPolyPrefix_74
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v0))
                              (coe v3))
                    (:) v5 v6 -> coe C_not'45'poly_3376
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notPolyB
d_notPolyB_3426 :: T_PolyKind_3374 -> Bool
d_notPolyB_3426 v0
  = case coe v0 of
      C_not'45'poly_3376 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_poly'45'dom_3378 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_poly'45'other_3380
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.domPolyB
d_domPolyB_3428 :: T_PolyKind_3374 -> Bool
d_domPolyB_3428 v0
  = case coe v0 of
      C_not'45'poly_3376 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_poly'45'dom_3378 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_poly'45'other_3380
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.constB
d_constB_3432 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 -> Bool
d_constB_3432 ~v0 v1 = du_constB_3432 v1
du_constB_3432 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 -> Bool
du_constB_3432 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isYesB
d_isYesB_3436 ::
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_isYesB_3436 ~v0 v1 = du_isYesB_3436 v1
du_isYesB_3436 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_isYesB_3436 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.synthForm?
d_synthForm'63'_3444 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> Bool
d_synthForm'63'_3444 ~v0 v1 v2 = du_synthForm'63'_3444 v1 v2
du_synthForm'63'_3444 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> Bool
du_synthForm'63'_3444 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_48 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v2
        -> coe d_notPolyB_3426 (coe du_polyKind_3416 (coe v0) (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v2
        -> coe
             du_constB_3432
             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v2 v3
        -> coe
             du_synthApp'63'_3456
             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_headView_274 (coe v2))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_58 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_60 v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe du_synthForm'63'_3444 (coe v0) (coe v2))
             (coe du_synthForm'63'_3444 (coe v0) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_62 v2 v3 v4 v5 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_64
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_66 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_68 v2 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_70 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_72 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_74 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.domainForm?
d_domainForm'63'_3452 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> Bool
d_domainForm'63'_3452 v0 v1 v2
  = let v3 = coe du_synthForm'63'_3444 (coe v1) (coe v2) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v4
           -> coe d_domPolyB_3428 (coe du_polyKind_3416 (coe v1) (coe v4))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe du_synthForm'63'_3444 (coe v1) (coe v2))
                (coe d_domainGen'63'_3468 (coe v4))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe du_synthForm'63'_3444 (coe v1) (coe v2))
                (coe d_domainApp'63'_3466 (coe v0) (coe v1) (coe v4) (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v4 v5
           -> coe du_synthForm'63'_3444 (coe v1) (coe v5)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.synthApp?
d_synthApp'63'_3456 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_Head_262 -> Bool
d_synthApp'63'_3456 ~v0 v1 = du_synthApp'63'_3456 v1
du_synthApp'63'_3456 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_Head_262 -> Bool
du_synthApp'63'_3456 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_hv'45'gen_264 v1
        -> coe
             d_synthGenB_3472 (coe v1)
             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v1))
      MAlonzo.Code.Once.TypeCheck.Scope.C_hv'45'gen'8321'_266 v1 v2
        -> coe
             du_notComb'8322'B_3476
             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v1))
      MAlonzo.Code.Once.TypeCheck.Scope.C_hv'45'gen'8322'_268 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_hv'45'lam_270
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_hv'45'other_272
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.domainApp?
d_domainApp'63'_3466 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> Bool
d_domainApp'63'_3466 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v5
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36
                  -> coe du_synthForm'63'_3444 (coe v1) (coe v3)
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v6))
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v3))
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v6))
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v3))
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28
                         -> coe
                              MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v6))
                              (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v3))
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.domainGen?
d_domainGen'63'_3468 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 -> Bool
d_domainGen'63'_3468 v0
  = coe
      du_isYesB_3436
      (coe
         MAlonzo.Code.Once.Generators.d_fromDomain'63'_138
         (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_kind_70 (coe v0)))
-- Once.TypeCheck.Elaborate.synthGenB
d_synthGenB_3472 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 -> Bool
d_synthGenB_3472 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe
                du_isYesB_3436
                (coe
                   MAlonzo.Code.Once.Generators.d_fromCodomain'63'_142
                   (coe
                      MAlonzo.Code.Once.Spec.Surface.Generators.d_kind_70 (coe v0))))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notComb₂B
d_notComb'8322'B_3476 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 -> Bool
d_notComb'8322'B_3476 ~v0 v1 = du_notComb'8322'B_3476 v1
du_notComb'8322'B_3476 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 -> Bool
du_notComb'8322'B_3476 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_3594 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferElab_3594 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v3
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_2824 (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal_256 (coe v0)
                (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_48 v3 v4
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_26 (coe v3)
                (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v3
        -> coe
             du_inferElabV'45'RResolved'45'aux_2756 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v3)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v3
        -> coe
             du_inferGen_3002 (coe v1) (coe v3)
             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v3 v4
        -> coe d_inferApp_3636 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v3 v4
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_34)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_58 v3 v4 v5
        -> coe
             du_inferElabV'45'RLet'45'aux_4090 (coe v0) (coe v1) (coe v3)
             (coe v5) (coe d_inferElab_3594 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_60 v3 v4
        -> coe
             du_inferElabV'45'RPair'45'aux_1816
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_62 v3 v4 v5 v6 v7
        -> coe
             du_inferElabV'45'RDestruct'45'aux_4106 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_64
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_164)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_66 v3
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_196 v3)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_68 v3 v4 v5 v6
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_float_204
                (MAlonzo.Code.Once.Spec.Surface.Syntax.d_signedDecimal_76
                   (coe v3) (coe v4) (coe v5) (coe v6)))
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_70 v3 v4
        -> coe
             du_inferElabV'45'RAnnot'45'aux_1868 (coe v0) (coe v4)
             (coe
                d_checkElab_3604 (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_72 v3 v4 v5
        -> coe
             du_inferElabV'45'RBinOp'45'aux_2208 (coe v0) (coe v3)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v4))
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_74 v3
        -> coe
             du_inferElabV'45'RNeg'45'aux_1968 (coe v0)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_3604 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab_3604 v0 v1 v2 v3
  = coe du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Elaborate.checkElab-wf
d_checkElab'45'wf_3614 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab'45'wf_3614 v0 v1 ~v2 v3 v4
  = du_checkElab'45'wf_3614 v0 v1 v3 v4
du_checkElab'45'wf_3614 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_checkElab'45'wf_3614 v0 v1 v2 v3
  = let v4
          = let v4 = d_inferElab_3594 (coe v0) (coe v1) (coe v2) in
            coe (coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v4)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v5
           -> let v6
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_2824 (coe v5)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal'45'go_170 (coe v0)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1))
                           (coe v5)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_named_132 (coe v1))
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_debruijn_134 (coe v1))) in
              coe (coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v6))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v5
           -> let v6
                    = coe
                        du_inferElabV'45'RResolved'45'aux_2756 (coe v0) (coe v1) (coe v5)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                           (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v5))) in
              coe
                (coe
                   d_checkElabV'45'RResolved'45'other_2852 (coe v0) (coe v1) (coe v5)
                   (coe v3) (coe v6))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v5
           -> let v6
                    = MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v5) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v7
                     -> coe
                          d_checkMapAt_3064 (coe v0) (coe v1) (coe v5) (coe v3)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.TargetView.du_arrowTarget_234 (coe v3))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
                     -> coe
                          du_embedOrSubsume_540 (coe v0) (coe v3)
                          (coe
                             du_inferGen_3002 (coe v1) (coe v5)
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
                     -> coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                             (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v5)))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
                     -> coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                             (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v5)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v5 v6
           -> coe d_checkApp_3762 (coe v0) (coe v1) (coe v5) (coe v6) (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v5 v6
           -> let v7
                    = coe
                        C_failure_128
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_36) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
                     -> case coe v9 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                            -> let v13
                                     = d_checkElab_3604
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
                                             -> let v21 = d_decideLeq_940 (coe v19) (coe v11) in
                                                coe
                                                  (case coe v21 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                       -> coe
                                                            C_success_126 (coe v20)
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_lam_38
                                                               v19 v15)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v16))
                                                            (coe v17)
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_80
                                                               (coe v5) (coe v11) (coe v19))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    C_failure_128 v14 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v7)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_60 v5 v6
           -> coe
                d_checkElabV'45'RPair'45'aux_4146 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3) (coe du_classifyRPairTarget_60 (coe v3))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.elabGiven
d_elabGiven_3626 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_GivenElabResult_140
d_elabGiven_3626 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_given'45'infer_264 (coe v0) (coe v3) (coe v4)
              (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v6
           -> coe
                d_given'45'res_1500 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4)
                (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v6
           -> let v7
                    = MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v8
                     -> coe
                          du_givenMap_3034 (coe v0) (coe v1) (coe v6) (coe v3)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Table.d_mapFrom'63'_316 (coe v0)
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                             (coe v6) (coe v3))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
                     -> coe
                          du_given'45'infer_264 (coe v0) (coe v3) (coe v4)
                          (coe
                             du_inferGen_3002 (coe v1) (coe v6)
                             (coe MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
                     -> coe
                          C_failure_162
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                             (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v6)))
                   MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
                     -> coe
                          C_failure_162
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                             (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v6)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v6 v7
           -> coe
                d_givenApp_4064 (coe v0) (coe v1) (coe v6) (coe v7) (coe v3)
                (coe v4) (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v6 v7
           -> let v8
                    = d_inferElab_3594
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
                            -> coe
                                 C_success_160 (coe v9) (coe v16)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v15 v11)
                                 (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_failure_100 v9 -> coe C_failure_162 (coe v9)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.inferApp
d_inferApp_3636 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferApp_3636 v0 v1 v2 v3
  = let v4 = d_appOther_3720 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v5
           -> coe
                d_inferAppGen_3646 (coe v0) (coe v1) (coe v5) (coe v3)
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v7
                  -> coe
                       d_inferAppGen'8321'_3668 (coe v0) (coe v1) (coe v2) (coe v7)
                       (coe v3)
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v7))
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v9
                         -> coe
                              du_inferAppGen'8322'_3680 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v9))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_56 v5 v6
           -> coe
                d_inferSpine_3738 (coe v0) (coe v1) (coe v2)
                (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.inferAppGen
d_inferAppGen_3646 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
d_inferAppGen_3646 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v5
        -> coe
             d_inferMapAt_3656 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Generators.d_fromDomain'63'_138
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_kind_70 (coe v2)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v3)
             (coe
                du_inferGen_3002 (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v2)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferMapAt
d_inferMapAt_3656 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferMapAt_3656 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       d_inferMapSpine_3124 (coe v0) (coe v1) (coe v2)
                       (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3)))
             else coe
                    seq (coe v6) (coe C_failure_100 (coe d_spineErr_2938 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferAppGen₁
d_inferAppGen'8321'_3668 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
d_inferAppGen'8321'_3668 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v6
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v4)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v4)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe
             d_inferSpine_3738 (coe v0) (coe v1) (coe v2)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferAppGen₂
d_inferAppGen'8322'_3680 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
d_inferAppGen'8322'_3680 v0 v1 v2 ~v3 v4 v5
  = du_inferAppGen'8322'_3680 v0 v1 v2 v4 v5
du_inferAppGen'8322'_3680 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_InferElabResult_82
du_inferAppGen'8322'_3680 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v5
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v3)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v3)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v3)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe
             d_inferSpine_3738 (coe v0) (coe v1) (coe v2)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.appOn
d_appOn_3688 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_appOn_3688 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v4))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v4))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v4))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           du_appAt_3710 (coe v9) (coe v11) (coe v12) (coe v13) (coe v5)
                           (coe v6) (coe v7)
                           (coe d_checkElab_3604 (coe v0) (coe v1) (coe v2) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v4))
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.appAt
d_appAt_3710 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_CheckElabResult_110 -> T_InferElabResult_82
d_appAt_3710 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11
  = du_appAt_3710 v3 v4 v5 v6 v7 v8 v9 v11
du_appAt_3710 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_CheckElabResult_110 -> T_InferElabResult_82
du_appAt_3710 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_126 v8 v9 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                      -> coe
                           C_success_98 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v2)
                                 (coe v8)))
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_app_54 v4 v8 v0 v2 v5 v9)
                           (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v6) (coe v10))
                           (coe v11)
                    MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                      -> coe
                           C_success_98
                           (coe
                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                              (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                              (coe
                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                              (coe v1))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v2)
                                 (coe v8)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_effApp_74 v4 v8 v0 v2
                              (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70) v5 v9)
                           (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v6) (coe v10))
                           (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe
                    C_success_98
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                       (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
                       (coe v1))
                    (coe
                       MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v4)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v2)
                          (coe v8)))
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_effApp_74 v4 v8 v0 v2
                       (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) v5 v9)
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v6) (coe v10))
                    (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_128 v8 -> coe C_failure_100 (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.appOther
d_appOther_3720 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_appOther_3720 v0 v1 v2 v3
  = let v4
          = d_appOn_3688
              (coe v0) (coe v1) (coe v3)
              (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v5
           -> coe
                d_appRes_3730 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe du_polyKind_3416 (coe v1) (coe v5))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.appRes
d_appRes_3730 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_PolyKind_3374 -> T_InferElabResult_82
d_appRes_3730 v0 v1 v2 v3 v4
  = case coe v4 of
      C_not'45'poly_3376
        -> coe
             d_appOn_3688 (coe v0) (coe v1) (coe v3)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
      C_poly'45'dom_3378
        -> coe
             d_inferSpine_3738 (coe v0) (coe v1) (coe v2)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
      C_poly'45'other_3380
        -> coe
             d_inferSpine_3738 (coe v0) (coe v1) (coe v2)
             (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_3738 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferSpine_3738 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe
             du_spineAt_3750 (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                d_elabGiven_3626 (coe v0) (coe v1) (coe v2) (coe v4)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
      C_failure_100 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineAt
d_spineAt_3750 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_GivenElabResult_140 -> T_InferElabResult_82
d_spineAt_3750 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_spineAt_3750 v2 v3 v4 v5 v6
du_spineAt_3750 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_GivenElabResult_140 -> T_InferElabResult_82
du_spineAt_3750 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_160 v5 v6 v7 v8 v9
        -> coe
             C_success_98 (coe v5)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v6)
                (coe
                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_app_54 v6 v1 v0
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v7 v2)
             (coe
                addInt (coe (1 :: Integer))
                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v3)))
             (coe v9)
      C_failure_162 v5 -> coe C_failure_100 (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkApp
d_checkApp_3762 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkApp_3762 v0 v1 v2 v3 v4
  = let v5
          = d_checkSubApp_3804
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v6
           -> coe
                d_checkAppGen_3776 (coe v0) (coe v1) (coe v2) (coe v6) (coe v3)
                (coe v4)
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v6))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v8
                  -> coe
                       d_checkAppGen'8321'_3792 (coe v0) (coe v1) (coe v2) (coe v8)
                       (coe v7) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_genKindView_308 (coe v8))
                _ -> coe v5
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.checkAppGen
d_checkAppGen_3776 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_CheckElabResult_110
d_checkAppGen_3776 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v7
        -> coe
             d_checkMapApp_3818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Generators.d_fromCodomain'63'_142
                (coe MAlonzo.Code.Once.Spec.Surface.Generators.d_kind_70 (coe v3)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe
             d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe
             d_checkComb'8321'_3844 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe
             d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAppGen₁
d_checkAppGen'8321'_3792 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_GenKindView_294 ->
  T_CheckElabResult_110
d_checkAppGen'8321'_3792 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'map_298 v8
        -> coe
             d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'const_300
        -> coe
             d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8321'_302
        -> coe
             d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
      MAlonzo.Code.Once.TypeCheck.Scope.C_gk'45'comb'8322'_304
        -> coe
             d_checkComb'8322'_3858 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkSubApp
d_checkSubApp_3804 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkSubApp_3804 v0 v1 v2 v3 v4
  = let v5 = d_inferApp_3636 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe (coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v5))
-- Once.TypeCheck.Elaborate.checkMapApp
d_checkMapApp_3818 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_checkMapApp_3818 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       du_checkMapApp'45'go_3832 (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Table.du_mapTo'63'_516
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                          (coe v3) (coe v5)))
             else coe
                    seq (coe v8)
                    (coe
                       d_checkSubApp_3804 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkMapApp-go
d_checkMapApp'45'go_3832 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CheckElabResult_110
d_checkMapApp'45'go_3832 v0 v1 v2 v3 ~v4 v5
  = du_checkMapApp'45'go_3832 v0 v1 v2 v3 v5
du_checkMapApp'45'go_3832 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CheckElabResult_110
du_checkMapApp'45'go_3832 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> let v8
                        = coe
                            du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v3) (coe v6) in
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
                                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_288 v9 v6 v7 v10)
                              (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                       C_failure_128 v9 -> coe v8
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_failure_128 (coe du_mapToErr_5060 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkComb₁
d_checkComb'8321'_3844 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkComb'8321'_3844 v0 v1 v2 v3 v4
  = let v5
          = coe
              C_failure_128
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                 (coe
                    MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_curry_32
           -> coe
                d_checkCurryOn_3986 (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_curryTarget_132 (coe v4))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36
           -> coe
                d_checkCataOn_3996 (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_cataTarget_28 (coe v4))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_ana_40
           -> coe
                d_checkAnaOn_4022 (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_anaTarget_66 (coe v4))
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.checkComb₂
d_checkComb'8322'_3858 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkComb'8322'_3858 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              C_failure_128
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                 (coe
                    MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v2))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12
           -> coe
                d_checkComposeOn_3908 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_arrowTarget_234 (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20
           -> coe
                d_checkPairOn_3870 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_pairTarget_168 (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28
           -> coe
                d_checkCaseOn_3896 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.TypeCheck.TargetView.du_caseTarget_202 (coe v5))
         _ -> coe v6)
-- Once.TypeCheck.Elaborate.checkPairOn
d_checkPairOn_3870 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_146 ->
  T_CheckElabResult_110
d_checkPairOn_3870 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_158
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
                             -> let v17
                                      = coe
                                          du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
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
                                                = coe
                                                    du_checkElab'45'wf_3614 (coe v0) (coe v1)
                                                    (coe v3)
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
                                                         MAlonzo.Code.Once.Surface.Syntax.C_fork''_342
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("pair" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_3884 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkPairLit_3884 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v6 of
         C_success_126 v7 v8 v9 v10
           -> let v11
                    = coe
                        du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v3) (coe v5) in
              coe
                (case coe v11 of
                   C_success_126 v12 v13 v14 v15
                     -> coe
                          C_success_126
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v7)
                             (coe v12))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_88 v7 v12 v8 v13)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9) (coe v14))
                          (coe v15)
                   C_failure_128 v12 -> coe v11
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_128 v7 -> coe v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCaseOn
d_checkCaseOn_3896 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_180 ->
  T_CheckElabResult_110
d_checkCaseOn_3896 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_192
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                             -> let v17
                                      = coe
                                          du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                             (coe v13)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v16))
                                             (coe v12)) in
                                coe
                                  (case coe v17 of
                                     C_success_126 v18 v19 v20 v21
                                       -> let v22
                                                = coe
                                                    du_checkElab'45'wf_3614 (coe v0) (coe v1)
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                       (coe v14)
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                          (coe v16))
                                                       (coe v12)) in
                                          coe
                                            (case coe v22 of
                                               C_success_126 v23 v24 v25 v26
                                                 -> coe
                                                      C_success_126
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                         (coe v18) (coe v23))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_copair''_324
                                                         v18 v23 v19 v24)
                                                      (coe
                                                         addInt (coe (1 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                            (coe v20) (coe v25)))
                                                      (coe v21)
                                               C_failure_128 v23 -> coe v22
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_128 v18 -> coe v17
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'other_196
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("case" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkComposeOn
d_checkComposeOn_3908 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_214 ->
  T_CheckElabResult_110
d_checkComposeOn_3908 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_224
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           d_checkCompose'45'route_3924 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v9) (coe v11) (coe v13)
                           (coe d_domainForm'63'_3452 (coe v0) (coe v1) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_228
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("compose" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-route
d_checkCompose'45'route_3924 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Bool -> T_CheckElabResult_110
d_checkCompose'45'route_3924 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_checkCompose'45'g_3938 (coe v0) (coe v1) (coe v2) (coe v5)
             (coe v6)
             (coe d_elabGiven_3626 (coe v0) (coe v1) (coe v3) (coe v4) (coe v6))
      else coe
             d_checkCompose'45'f_3952 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe d_inferElab_3594 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkCompose-g
d_checkCompose'45'g_3938 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_140 -> T_CheckElabResult_110
d_checkCompose'45'g_3938 v0 v1 v2 ~v3 v4 v5 v6
  = du_checkCompose'45'g_3938 v0 v1 v2 v4 v5 v6
du_checkCompose'45'g_3938 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_140 -> T_CheckElabResult_110
du_checkCompose'45'g_3938 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_160 v6 v7 v8 v9 v10
        -> let v11
                 = coe
                     du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v6)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v4))
                        (coe v3)) in
           coe
             (case coe v11 of
                C_success_126 v12 v13 v14 v15
                  -> coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v12 v7 v6 v13 v8)
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v14) (coe v9)))
                       (coe v15)
                C_failure_128 v12 -> coe v11
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_162 v6 -> coe C_failure_128 (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_3952 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkCompose'45'f_3952 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_98 v7 v8 v9 v10 v11
        -> let v12
                 = coe
                     C_failure_128
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_96) in
           coe
             (case coe v7 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                -> coe
                                     d_checkCompose'45'f'45'sub_3976 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v13) (coe v4) (coe v15) (coe v5) (coe v17)
                                     (coe v8) (coe v9) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                        (coe v0) (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v16)
                                              (coe v5))
                                           (coe v4)))
                              _ -> coe v12
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v12)
      C_failure_100 v7 -> coe C_failure_128 (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f-sub
d_checkCompose'45'f'45'sub_3976 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_checkCompose'45'f'45'sub_3976 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = case coe v12 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then case coe v14 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                      -> let v16
                               = coe
                                   du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                                      (coe v4)) in
                         coe
                           (case coe v16 of
                              C_success_126 v17 v18 v19 v20
                                -> coe
                                     C_success_126
                                     (coe
                                        MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v17)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v9 v17 v4
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_coerce_230
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v4)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v8))
                                              (coe v6))
                                           v15 v10)
                                        v18)
                                     (coe
                                        addInt (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11)
                                           (coe v19)))
                                     (coe v20)
                              C_failure_128 v17 -> coe v16
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v14)
                    (coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v7))
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                             (coe v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_3986 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_108 ->
  T_CheckElabResult_110
d_checkCurryOn_3986 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'at_122
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
                      -> case coe v14 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v16 v17
                             -> let v18
                                      = coe
                                          du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                             (coe
                                                MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v10)
                                                (coe v13))
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v17))
                                             (coe v15)) in
                                coe
                                  (case coe v18 of
                                     C_success_126 v19 v20 v21 v22
                                       -> coe
                                            C_success_126 (coe v19)
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_curry''_360 v20)
                                            (coe addInt (coe (1 :: Integer)) (coe v21)) (coe v22)
                                     C_failure_128 v19 -> coe v18
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_curry'45'other_126
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("curry" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_3996 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_8 ->
  T_CheckElabResult_110
d_checkCataOn_3996 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_18
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                             -> coe
                                  d_checkCataGo_4012 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10)
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_4012 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
d_checkCataGo_4012 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = coe
                     du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
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
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v9
                          (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v7 v10)
                       (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                C_failure_128 v9 -> coe v8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_4022 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_38 ->
  T_CheckElabResult_110
d_checkAnaOn_4022 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_loop'45'at_46
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    du_checkLoop_4050
                    (coe
                       d_checkElab_3604 (coe v0) (coe v1) (coe v2)
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
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v13 v14
                      -> coe
                           du_checkAnaGo_4040 (coe v0) (coe v1) (coe v2) (coe v13) (coe v10)
                           (coe v14)
                           (coe
                              MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_ana'45'other_60
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_4040 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
d_checkAnaGo_4040 v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_checkAnaGo_4040 v0 v1 v2 v3 v4 v6 v7
du_checkAnaGo_4040 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkAnaGo_4040 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = coe
                     du_checkElab'45'wf_3614 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v4)
                        (coe
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                           (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v5)))
                        (coe
                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                           (coe v4))) in
           coe
             (case coe v8 of
                C_success_126 v9 v10 v11 v12
                  -> coe
                       C_success_126
                       (coe
                          MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_ana_394 v9
                          (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v7 v10)
                       (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                C_failure_128 v9 -> coe v8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkLoop
d_checkLoop_4050 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_CheckElabResult_110
d_checkLoop_4050 ~v0 ~v1 ~v2 ~v3 v4 = du_checkLoop_4050 v4
du_checkLoop_4050 :: T_CheckElabResult_110 -> T_CheckElabResult_110
du_checkLoop_4050 v0
  = case coe v0 of
      C_success_126 v1 v2 v3 v4
        -> coe
             C_success_126
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_406 v1 v2)
             (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)
      C_failure_128 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.givenApp
d_givenApp_4064 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_givenApp_4064 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe du_given'45'infer_264 (coe v0) (coe v4) (coe v5) (coe v6) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v8
           -> case coe v8 of
                MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36
                  -> coe
                       d_givenCata_3196 (coe v0) (coe v1) (coe v4) (coe v5)
                       (coe d_inferElab_3594 (coe v0) (coe v1) (coe v3))
                _ -> coe v7
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_54 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_52 v10
                  -> case coe v10 of
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12
                         -> let v11
                                  = d_elabGiven_3626 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                            coe
                              (case coe v11 of
                                 C_success_160 v12 v13 v14 v15 v16
                                   -> let v17
                                            = d_elabGiven_3626
                                                (coe v0) (coe v1) (coe v9) (coe v12) (coe v5) in
                                      coe
                                        (case coe v17 of
                                           C_success_160 v18 v19 v20 v21 v22
                                             -> coe
                                                  C_success_160 (coe v18)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                     (coe v19)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v13)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_comp''_306
                                                     v19 v13 v12 v20 v14)
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v21) (coe v15)))
                                                  (coe v22)
                                           C_failure_162 v18 -> coe v17
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_162 v12 -> coe v11
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20
                         -> let v11
                                  = d_elabGiven_3626 (coe v0) (coe v1) (coe v9) (coe v4) (coe v5) in
                            coe
                              (case coe v11 of
                                 C_success_160 v12 v13 v14 v15 v16
                                   -> let v17
                                            = d_elabGiven_3626
                                                (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                                      coe
                                        (case coe v17 of
                                           C_success_160 v18 v19 v20 v21 v22
                                             -> coe
                                                  C_success_160
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                                     (coe v12) (coe v18))
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                     (coe v13) (coe v19))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_fork''_342
                                                     v13 v19 v14 v20)
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v15) (coe v21)))
                                                  (coe v22)
                                           C_failure_162 v18 -> coe v17
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_failure_162 v12 -> coe v11
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28
                         -> coe
                              d_givenCase_4078 (coe v0) (coe v1) (coe v9) (coe v3) (coe v4)
                              (coe v5)
                              (coe MAlonzo.Code.Once.TypeCheck.Table.du_sumV_192 (coe v4))
                       _ -> coe v7
                _ -> coe v7
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.givenCase
d_givenCase_4078 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Table.T_SumV_174 ->
  T_GivenElabResult_140
d_givenCase_4078 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Table.C_sum'45'at_182
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> let v11
                        = d_elabGiven_3626 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) in
                  coe
                    (case coe v11 of
                       C_success_160 v12 v13 v14 v15 v16
                         -> let v17
                                  = d_elabGiven_3626
                                      (coe v0) (coe v1) (coe v3) (coe v10) (coe v5) in
                            coe
                              (case coe v17 of
                                 C_success_160 v18 v19 v20 v21 v22
                                   -> coe
                                        du_given'45'case'45'join_2448 (coe v0) (coe v9) (coe v10)
                                        (coe v5) (coe v12) (coe v13) (coe v14) (coe v15) (coe v18)
                                        (coe v19) (coe v20) (coe v21) (coe v22)
                                        (coe
                                           MAlonzo.Code.Once.Type.Join.d_join'63'_638 (coe v0)
                                           (coe v12) (coe v18))
                                 C_failure_162 v18 -> coe v17
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_failure_162 v12 -> coe v11
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Table.C_sum'45'other_186
        -> coe
             C_failure_162
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("case" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_4090 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux_4090 v0 v1 v2 ~v3 v4 v5
  = du_inferElabV'45'RLet'45'aux_4090 v0 v1 v2 v4 v5
du_inferElabV'45'RLet'45'aux_4090 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux_4090 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> coe
             du_inferElabV'45'RLet'45'aux2_2260 (coe v5) (coe v6) (coe v7)
             (coe v8)
             (coe
                d_inferElab_3594 (coe v0)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                   (coe v2) (coe v5))
                (coe v3))
      C_failure_100 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_4106 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'aux_4106 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RDestruct'45'aux_4106 v0 v1 v3 v4 v5 v6 v7
du_inferElabV'45'RDestruct'45'aux_4106 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'aux_4106 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_98 v7 v8 v9 v10 v11
        -> case coe v7 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v12
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    du_inferElabV'45'RDestruct'45'auxL_4134 (coe v0) (coe v1) (coe v4)
                    (coe v5) (coe v12) (coe v13) (coe v8) (coe v9) (coe v10)
                    (coe
                       d_inferElab_3594 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                          (coe v2) (coe v12))
                       (coe v3))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v12
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v12 v13
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_100
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_56)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_4134 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'auxL_4134 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
                                       v8 v9 v10 v11 ~v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_4134
      v0 v1 v5 v6 v7 v8 v9 v10 v11 v13
du_inferElabV'45'RDestruct'45'auxL_4134 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'auxL_4134 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      C_success_98 v10 v11 v12 v13 v14
        -> case coe v11 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v16 v17
               -> coe
                    du_inferElabV'45'RDestruct'45'auxR_2540 (coe v0) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v10) (coe v16) (coe v17) (coe v12)
                    (coe v13)
                    (coe
                       d_inferElab_3594 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                          (coe v2) (coe v5))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_4146 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_RPairTarget_32 -> T_CheckElabResult_110
d_checkElabV'45'RPair'45'aux_4146 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_rpt'45'prod_40
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
               -> coe
                    d_checkPairLit_3884 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
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
                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
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
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("pair" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.mapToErr
d_mapToErr_5060 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_mapToErr_5060 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_mapToErr_5060 v5
du_mapToErr_5060 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
du_mapToErr_5060 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
              (coe
                 MAlonzo.Code.Once.Spec.Surface.Generators.d_word_46 (coe v0)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48
         MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
           -> coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50
         _ -> coe v1)
