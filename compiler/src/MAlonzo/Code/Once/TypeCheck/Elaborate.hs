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
import qualified MAlonzo.Code.Data.Maybe.Base
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
import qualified MAlonzo.Code.Once.Spec.Float.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Operator
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Numeric
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
import qualified MAlonzo.Code.Once.TypeCheck.NumTable
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
                                                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
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
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_374 v4
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
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v3 v10 v4)
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
-- Once.TypeCheck.Elaborate.specId
d_specId_570 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specId_570 ~v0 ~v1 = du_specId_570
du_specId_570 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specId_570
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_580 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specFst_580 ~v0 ~v1 ~v2 = du_specFst_580
du_specFst_580 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specFst_580
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_592 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specSnd_592 ~v0 ~v1 ~v2 = du_specSnd_592
du_specSnd_592 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specSnd_592
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_snd_48)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_604 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInl_604 ~v0 ~v1 ~v2 = du_specInl_604
du_specInl_604 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInl_604
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_inl_54)
-- Once.TypeCheck.Elaborate.specInr
d_specInr_616 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInr_616 ~v0 ~v1 ~v2 = du_specInr_616
du_specInr_616 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInr_616
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_inr_60)
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_622 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specUnitGen_622 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
-- Once.TypeCheck.Elaborate.specPair
d_specPair_632 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specPair_632 v0 ~v1 ~v2 = du_specPair_632 v0
du_specPair_632 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specPair_632 v0
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
d_specTerminal_644 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specTerminal_644 ~v0 ~v1 = du_specTerminal_644
du_specTerminal_644 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specTerminal_644
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_652 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specInitial_652 ~v0 ~v1 = du_specInitial_652
du_specInitial_652 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specInitial_652
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
      (coe MAlonzo.Code.Once.IR.C_initial_76)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCurry_664 v0 v1 ~v2 = du_specCurry_664 v0 v1
du_specCurry_664 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCurry_664 v0 v1
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
d_specApply_678 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specApply_678 v0 v1
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
d_specCompose_692 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCompose_692 v0 v1 ~v2 = du_specCompose_692 v0 v1
du_specCompose_692 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCompose_692 v0 v1
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
d_specCase_708 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_specCase_708 v0 v1 ~v2 = du_specCase_708 v0 v1
du_specCase_708 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_specCase_708 v0 v1
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
d_extract'45'morph'45'aux_734 ::
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
d_extract'45'morph'45'aux_734 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_extract'45'morph'45'aux_734 v4 v8
du_extract'45'morph'45'aux_734 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_734 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_754 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_754 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_extract'45'morph_754 v4 v5 v6 v7
du_extract'45'morph_754 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_754 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_734
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_764 a0 a1 a2 = ()
data T_WellFormedFView_764
  = C_wfv'45'yes_774 MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_wfv'45'no_776
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_784 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_764
d_inspectWellFormedF_784 ~v0 v1 v2
  = du_inspectWellFormedF_784 v1 v2
du_inspectWellFormedF_784 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_WellFormedFView_764
du_inspectWellFormedF_784 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468 (coe v0)
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_wfv'45'yes_774 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_776
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_806 = ()
data T_AppSpine_806
  = C_mkSpine_816 MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44
                  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_812 ::
  T_AppSpine_806 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44
d_head_812 v0
  = case coe v0 of
      C_mkSpine_816 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_814 ::
  T_AppSpine_806 -> [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44]
d_args_814 v0
  = case coe v0 of
      C_mkSpine_816 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_818 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 -> T_AppSpine_806
d_spineOf_818 v0
  = coe
      du_go_826 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_826 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44] -> T_AppSpine_806
d_go_826 ~v0 v1 v2 = du_go_826 v1 v2
du_go_826 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44] -> T_AppSpine_806
du_go_826 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v2
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_48 v2 v3
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v2
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v2 v3
        -> coe
             du_go_826 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v2 v3
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_56 v2 v3 v4
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v2 v3
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_60 v2 v3 v4 v5 v6
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_62
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_64 v2
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_66 v2 v3 v4 v5
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_68 v2 v3
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_70 v2 v3 v4
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v2
        -> coe C_mkSpine_816 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_914 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_914 v0
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
d_matchInferResult_924 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_matchInferResult_924 v0 ~v1 ~v2 v3 v4
  = du_matchInferResult_924 v0 v3 v4
du_matchInferResult_924 ::
  Integer ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_matchInferResult_924 v0 v1 v2
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
d_FunProjection_974 a0 a1 a2 = ()
data T_FunProjection_974
  = C_isFun_990 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_isEff_1002 MAlonzo.Code.Once.Spec.Grade.T_Purity_40
                 MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notFun_1004 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1012 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_FunProjection_974
d_asFun_1012 v0 ~v1 ~v2 v3 = du_asFun_1012 v0 v3
du_asFun_1012 ::
  Integer -> T_InferElabResult_82 -> T_FunProjection_974
du_asFun_1012 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notFun_1004
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
                                         C_isFun_990 (coe v7) (coe v10) (coe v9) (coe v3) (coe v4)
                                         (coe v5) (coe v6)
                                  MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                    -> case coe v10 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_notFun_1004
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_notFun_1004
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                   (coe v0) (coe v2))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_isEff_1002 (coe v11)
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70)
                                                (coe v7) (coe v9) (coe v3) (coe v4) (coe v5)
                                                (coe v6)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_eff_44
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         C_notFun_1004
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         C_notFun_1004
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                            (coe v0) (coe v2))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         C_isEff_1002 (coe v11)
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) (coe v7)
                                         (coe v9) (coe v3) (coe v4) (coe v5) (coe v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notFun_1004
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                       (coe (0 :: Integer)) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notFun_1004 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1102 a0 a1 a2 = ()
data T_IntProjection_1102
  = C_isInt_1112 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 Integer Integer |
    C_notInt_1114 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 -> T_IntProjection_1102
d_asInt_1122 v0 ~v1 ~v2 v3 = du_asInt_1122 v0 v3
du_asInt_1122 ::
  Integer -> T_InferElabResult_82 -> T_IntProjection_1102
du_asInt_1122 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v7
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v7
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66 (coe v0)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2))
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe C_isInt_1112 (coe v3) (coe v4) (coe v5) (coe v6)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_notInt_1114
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                       (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v2 -> coe C_notInt_1114 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.numErr
d_numErr_1158 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_numErr_1158 v0 v1 v2
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
d_notNumeric_1212 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_notNumeric_1212 v0 ~v1 ~v2 v3 = du_notNumeric_1212 v0 v3
du_notNumeric_1212 ::
  Integer ->
  T_InferElabResult_82 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
du_notNumeric_1212 v0 v1
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
d_decideLeq_1242 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1242 v0 v1
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
d_inferElab'45'RApp'45'id_1248 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElab'45'RApp'45'id_1248 ~v0 v1 v2
  = du_inferElab'45'RApp'45'id_1248 v1 v2
du_inferElab'45'RApp'45'id_1248 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElab'45'RApp'45'id_1248 v0 v1
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
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isGround-inj₂→¬Ground
d_isGround'45'inj'8322''8594''172'Ground_1268 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_isGround'45'inj'8322''8594''172'Ground_1268 = erased
-- Once.TypeCheck.Elaborate.given-poly-k
d_given'45'poly'45'k_1312 ::
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
d_given'45'poly'45'k_1312 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 ~v9 ~v10
                          ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20
  = du_given'45'poly'45'k_1312 v0 v1 v2 v3 v4 v6 v8 v19 v20
du_given'45'poly'45'k_1312 ::
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
du_given'45'poly'45'k_1312 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
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
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_254 v2))
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
d_given'45'poly'45'π_1400 ::
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
d_given'45'poly'45'π_1400 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_given'45'poly'45'π_1400 v0 v1 v2 v3 v4 v6 v8 v9 v18 v20
du_given'45'poly'45'π_1400 ::
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
du_given'45'poly'45'π_1400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> if coe v10
             then case coe v11 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                      -> coe
                           du_given'45'poly'45'k_1312 (coe v0) (coe v1) (coe v2) (coe v3)
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
d_given'45'poly'45'm_1492 ::
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
d_given'45'poly'45'm_1492 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
  = du_given'45'poly'45'm_1492 v0 v1 v2 v3 v4 v6 v7 v8 v9 v18
du_given'45'poly'45'm_1492 ::
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
du_given'45'poly'45'm_1492 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             du_given'45'poly'45'π_1400 (coe v0) (coe v1) (coe v2) (coe v3)
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
d_given'45'poly'45'd_1572 ::
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
d_given'45'poly'45'd_1572 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
                          ~v12 ~v13 ~v14 ~v15 ~v16 v17
  = du_given'45'poly'45'd_1572 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v17
du_given'45'poly'45'd_1572 ::
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
du_given'45'poly'45'd_1572 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then coe
                    seq (coe v12)
                    (coe
                       du_given'45'poly'45'm_1492 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v6) (coe v7) (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Once.Type.Match.d_instantiate_100 (coe v0) (coe v7)
                          (coe v3)))
             else coe seq (coe v12) (coe C_failure_162 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly-a
d_given'45'poly'45'a_1636 ::
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
d_given'45'poly'45'a_1636 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 v13
  = du_given'45'poly'45'a_1636 v0 v1 v2 v3 v4 v5 v6 v13
du_given'45'poly'45'a_1636 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_GivenElabResult_140
du_given'45'poly'45'a_1636 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> coe
                                  du_given'45'poly'45'd_1572 (coe v0) (coe v1) (coe v2) (coe v3)
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
d_given'45'poly'45'g_1702 ::
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
d_given'45'poly'45'g_1702 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 v12 ~v13
  = du_given'45'poly'45'g_1702 v0 v1 v2 v3 v4 v5 v6 v12
du_given'45'poly'45'g_1702 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_GivenElabResult_140
du_given'45'poly'45'g_1702 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe C_failure_162 (coe v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             seq (coe v8)
             (coe
                du_given'45'poly'45'a_1636 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Type.Determined.d_arrowSchema'63'_626 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-poly
d_given'45'poly_1760 ::
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
d_given'45'poly_1760 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 v10 ~v11
  = du_given'45'poly_1760 v0 v1 v2 v3 v4 v5 v6 v8 v10
du_given'45'poly_1760 ::
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
du_given'45'poly_1760 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                     du_given'45'poly'45'g_1702 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v10)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_162 (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.given-res
d_given'45'res_1824 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_given'45'res_1824 v0 v1 v2 v3 v4 v5
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
                                  du_given'45'poly_1760 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
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
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878 ::
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
d_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878 v0 v1 v2 v3 ~v4 v5
                                                 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878
      v0 v1 v2 v3 v5 v12
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878 v0 v1 v2 v3 v4 v5
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
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_254 v2)
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
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934 ::
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
d_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934 v0 v1 v2 v3 v4
                                                   v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934
      v0 v1 v2 v3 v4 v5 v11
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934 v0 v1 v2 v3 v4
                                                    v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe C_failure_128 (coe v4)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             seq (coe v7)
             (coe
                du_checkElabV'45'RVar'45'poly'45'inst'45'aux_1878 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v5)
                (coe
                   MAlonzo.Code.Once.Type.Rigid.d_kindedInstance'63'_586 (coe v0)
                   (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                   (coe v5) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-poly-check-aux
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1986 ::
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
d_checkElabV'45'RVar'45'poly'45'check'45'aux_1986 v0 v1 v2 v3 v4 v5
                                                  ~v6 v7 ~v8 v9 ~v10
  = du_checkElabV'45'RVar'45'poly'45'check'45'aux_1986
      v0 v1 v2 v3 v4 v5 v7 v9
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1986 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'poly'45'check'45'aux_1986 v0 v1 v2 v3 v4
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
                                     du_checkElabV'45'RVar'45'poly'45'ground'45'aux_1934 (coe v0)
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                                     (coe MAlonzo.Code.Once.Type.d_isGround_98 (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe C_failure_128 (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044 ::
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
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6 ~v7 v8 ~v9
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044
      v0 v1 v2 v5 v8
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044 v0 v1 v2 v3 v4
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
             (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_254 v2)
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
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 v0 v1 v2 ~v3 ~v4
                                                   v5 ~v6
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 v0 v1 v2 v5
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_2044 (coe v0)
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
d_inferElabV'45'RVar'45'poly'45'aux_2114 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'poly'45'aux_2114 v0 v1 v2 ~v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'aux_2114 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'aux_2114 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_InferElabResult_82
du_inferElabV'45'RVar'45'poly'45'aux_2114 v0 v1 v2
  = coe
      du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_2084 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_10
         (coe MAlonzo.Code.Once.TypeCheck.Scope.d_polys_138 (coe v1))
         (coe v2))
-- Once.TypeCheck.Elaborate.determinedErr
d_determinedErr_2128 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
d_determinedErr_2128 ~v0 ~v1 v2 v3 = du_determinedErr_2128 v2 v3
du_determinedErr_2128 ::
  T_InferElabResult_82 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18
du_determinedErr_2128 v0 v1
  = case coe v0 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_failure_100 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.a⇒b
d_a'8658'b_2132 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_a'8658'b_2132 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32
      (coe v0) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1)
-- Once.TypeCheck.Elaborate.schema-id
d_schema'45'id_2138 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'id_2138
  = coe
      d_a'8658'b_2132
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("a" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("a" :: Data.Text.Text)))
-- Once.TypeCheck.Elaborate.schema-fst
d_schema'45'fst_2140 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'fst_2140
  = coe
      d_a'8658'b_2132
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
         (coe
            MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
            (coe ("a" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
            (coe ("b" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("a" :: Data.Text.Text)))
-- Once.TypeCheck.Elaborate.schema-snd
d_schema'45'snd_2142 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'snd_2142
  = coe
      d_a'8658'b_2132
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
         (coe
            MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
            (coe ("a" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
            (coe ("b" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("b" :: Data.Text.Text)))
-- Once.TypeCheck.Elaborate.schema-terminal
d_schema'45'terminal_2144 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'terminal_2144
  = coe
      d_a'8658'b_2132
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("a" :: Data.Text.Text)))
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20)
-- Once.TypeCheck.Elaborate.schema-initial
d_schema'45'initial_2146 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'initial_2146
  = coe
      d_a'8658'b_2132
      (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22)
      (coe
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
         (coe ("a" :: Data.Text.Text)))
-- Once.TypeCheck.Elaborate.schema-inl
d_schema'45'inl_2148 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'inl_2148
  = coe
      d_a'8658'b_2132
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
-- Once.TypeCheck.Elaborate.schema-inr
d_schema'45'inr_2150 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_schema'45'inr_2150
  = coe
      d_a'8658'b_2132
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
-- Once.TypeCheck.Elaborate.elabGivenLeaf
d_elabGivenLeaf_2162 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_elabGivenLeaf_2162 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_given'45'res_1824
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
           -> coe
                du_withUnit_320
                (coe
                   C_failure_162
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                      (coe ("id" :: Data.Text.Text))))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        C_success_160 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                           (coe MAlonzo.Code.Once.IR.C_id_20))
                        (coe (0 :: Integer)) (coe (0 :: Integer))))
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
           -> let v8
                    = coe
                        C_failure_162
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                           (coe ("fst" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                                 (coe ("a" :: Data.Text.Text)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                                 (coe ("b" :: Data.Text.Text))))
                           (coe v3)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_320
                          (coe
                             C_failure_162
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                (coe ("fst" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  C_success_160 (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
           -> let v8
                    = coe
                        C_failure_162
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                           (coe ("snd" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                                 (coe ("a" :: Data.Text.Text)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42
                                 (coe ("b" :: Data.Text.Text))))
                           (coe v3)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                     -> coe
                          du_withUnit_320
                          (coe
                             C_failure_162
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                (coe ("snd" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v11 ->
                                coe
                                  C_success_160 (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                     (coe MAlonzo.Code.Once.IR.C_snd_48))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
           -> coe
                du_withUnit_320
                (coe
                   C_failure_162
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                      (coe ("terminal" :: Data.Text.Text))))
                (coe v4)
                (coe
                   (\ v8 ->
                      coe
                        C_success_160 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                           (coe MAlonzo.Code.Once.IR.C_terminal_72))
                        (coe (0 :: Integer)) (coe (0 :: Integer))))
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
           -> let v8
                    = coe
                        C_failure_162
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                           (coe ("initial" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22) (coe v3)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Once.Spec.Type.C_Void_20
                     -> coe
                          du_withUnit_320
                          (coe
                             C_failure_162
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                (coe ("initial" :: Data.Text.Text))))
                          (coe v4)
                          (coe
                             (\ v9 ->
                                coe
                                  C_success_160 (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                     (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                     (coe MAlonzo.Code.Once.IR.C_initial_76))
                                  (coe (0 :: Integer)) (coe (0 :: Integer))))
                   _ -> coe v8)
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.outIR
d_outIR_2242 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_outIR_2242 ~v0 ~v1 v2 ~v3 v4 = du_outIR_2242 v2 v4
du_outIR_2242 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_outIR_2242 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_Out_110
      (coe
         MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v0)
         (coe v1))
-- Once.TypeCheck.Elaborate.inferOutGo
d_inferOutGo_2272 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferOutGo_2272 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_inferOutGo_2272 v0 v1 v3 v4 v5 v6 v7 v8 v9
du_inferOutGo_2272 ::
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
du_inferOutGo_2272 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v4
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))
                       (coe du_outIR_2242 (coe v2) (coe v9)) v5)
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
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v4
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3))
                       (coe
                          MAlonzo.Code.Once.IR.C_curry_84
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe v0)
                                (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v2) (coe v3)))
                             (coe du_outIR_2242 (coe v2) (coe v9))
                             (coe MAlonzo.Code.Once.IR.C_fst_42)))
                       v5)
                    (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("Out" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutAt
d_inferOutAt_2342 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  T_InferElabResult_82
d_inferOutAt_2342 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferOutAt_2342 v0 v1 v3 v4 v5 v6 v7 v8
du_inferOutAt_2342 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_NuView_260 ->
  T_InferElabResult_82
du_inferOutAt_2342 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_nu'45'at_268
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
               -> coe
                    du_inferOutGo_2272 (coe v0) (coe v1) (coe v10) (coe v11) (coe v3)
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("Out" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOutOn
d_inferOutOn_2378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferOutOn_2378 v0 v1 ~v2 v3 = du_inferOutOn_2378 v0 v1 v3
du_inferOutOn_2378 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferOutOn_2378 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_inferOutAt_2342 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
             (coe MAlonzo.Code.Once.TypeCheck.TargetView.du_nuView_278 (coe v3))
      C_failure_100 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstAt
d_inferFstAt_2416 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
d_inferFstAt_2416 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferFstAt_2416 v1 v3 v4 v5 v6 v7 v8
du_inferFstAt_2416 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
du_inferFstAt_2416 v0 v1 v2 v3 v4 v5 v6
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
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v2 v1
                       (coe MAlonzo.Code.Once.IR.C_fst_42) v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_52)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferFstOn
d_inferFstOn_2452 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferFstOn_2452 ~v0 v1 ~v2 v3 = du_inferFstOn_2452 v1 v3
du_inferFstOn_2452 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferFstOn_2452 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferFstAt_2416 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndAt
d_inferSndAt_2490 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
d_inferSndAt_2490 ~v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferSndAt_2490 v1 v3 v4 v5 v6 v7 v8
du_inferSndAt_2490 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ProdView_320 ->
  T_InferElabResult_82
du_inferSndAt_2490 v0 v1 v2 v3 v4 v5 v6
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
                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v2 v1
                       (coe MAlonzo.Code.Once.IR.C_snd_48) v3)
                    (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_prod'45'other_332
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_54)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSndOn
d_inferSndOn_2526 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferSndOn_2526 ~v0 v1 ~v2 v3 = du_inferSndOn_2526 v1 v3
du_inferSndOn_2526 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferSndOn_2526 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferSndAt_2490 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_prodView_338 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyAt
d_inferApplyAt_2564 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  T_InferElabResult_82
d_inferApplyAt_2564 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_inferApplyAt_2564 v0 v1 v3 v4 v5 v6 v7 v8
du_inferApplyAt_2564 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ApplyView_286 ->
  T_InferElabResult_82
du_inferApplyAt_2564 v0 v1 v2 v3 v4 v5 v6 v7
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
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286
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
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286
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
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286
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
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("apply" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferApplyOn
d_inferApplyOn_2758 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferApplyOn_2758 v0 v1 ~v2 v3 = du_inferApplyOn_2758 v0 v1 v3
du_inferApplyOn_2758 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferApplyOn_2758 v0 v1 v2
  = case coe v2 of
      C_success_98 v3 v4 v5 v6 v7
        -> coe
             du_inferApplyAt_2564 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.TypeCheck.TargetView.du_applyView_308 (coe v3))
      C_failure_100 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_2788 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RPair'45'aux_2788 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RPair'45'aux_2788 v4 v5
du_inferElabV'45'RPair'45'aux_2788 ::
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RPair'45'aux_2788 v0 v1
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
d_inferElabV'45'RAnnot'45'aux_2840 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
d_inferElabV'45'RAnnot'45'aux_2840 v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RAnnot'45'aux_2840 v0 v3 v4
du_inferElabV'45'RAnnot'45'aux_2840 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_InferElabResult_82
du_inferElabV'45'RAnnot'45'aux_2840 v0 v1 v2
  = case coe v2 of
      C_success_126 v3 v4 v5 v6
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v1))
             (coe v3) (coe v4) (coe v5) (coe v6)
      C_failure_128 v3 -> coe C_failure_100 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-has
d_inferElabV'45'RNeg'45'has_2876 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferElabV'45'RNeg'45'has_2876 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RNeg'45'has_2876 v2 v3 v4 v5 v6 v7
du_inferElabV'45'RNeg'45'has_2876 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
du_inferElabV'45'RNeg'45'has_2876 v0 v1 v2 v3 v4 v5
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
                              MAlonzo.Code.Once.Surface.Syntax.C_num_216 v0
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
d_inferElabV'45'RNeg'45'num_2912 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
d_inferElabV'45'RNeg'45'num_2912 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RNeg'45'num_2912 v0 v2 v3 v4 v5 v6 v7
du_inferElabV'45'RNeg'45'num_2912 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82
du_inferElabV'45'RNeg'45'num_2912 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v7
        -> coe
             du_inferElabV'45'RNeg'45'has_2876 (coe v7) (coe v2) (coe v3)
             (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.TypeCheck.NumTable.d_has'63'_44 (coe v7)
                (coe MAlonzo.Code.Once.Spec.Theory.C_Neg_18))
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                d_numErr_1158 (coe v0) (coe MAlonzo.Code.Once.Spec.Theory.C_int_8)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RNeg-aux
d_inferElabV'45'RNeg'45'aux_2940 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RNeg'45'aux_2940 v0 ~v1 ~v2 v3
  = du_inferElabV'45'RNeg'45'aux_2940 v0 v3
du_inferElabV'45'RNeg'45'aux_2940 ::
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RNeg'45'aux_2940 v0 v1
  = case coe v1 of
      C_success_98 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RNeg'45'num_2912 (coe v0) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v2))
      C_failure_100 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-has
d_inferElabV'45'RBinOp'45'has_2978 ::
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
d_inferElabV'45'RBinOp'45'has_2978 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10
  = du_inferElabV'45'RBinOp'45'has_2978 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_inferElabV'45'RBinOp'45'has_2978 ::
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
du_inferElabV'45'RBinOp'45'has_2978 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
d_inferElabV'45'RBinOp'45'num_3028 ::
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
d_inferElabV'45'RBinOp'45'num_3028 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8 v9
                                   v10 v11
  = du_inferElabV'45'RBinOp'45'num_3028 v2 v3 v5 v6 v7 v8 v9 v10 v11
du_inferElabV'45'RBinOp'45'num_3028 ::
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
du_inferElabV'45'RBinOp'45'num_3028 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       du_inferElabV'45'RBinOp'45'has_2978 (coe v0) (coe v1) (coe v2)
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
d_inferElabV'45'RBinOp'45'R_3078 ::
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
d_inferElabV'45'RBinOp'45'R_3078 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11
  = du_inferElabV'45'RBinOp'45'R_3078
      v0 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_inferElabV'45'RBinOp'45'R_3078 ::
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
du_inferElabV'45'RBinOp'45'R_3078 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v11
        -> coe
             du_inferElabV'45'RBinOp'45'num_3028 (coe v1) (coe v2) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.TypeCheck.NumTable.d__'8799''8319'__38 (coe v2)
                (coe v11))
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_112
                (coe d_numErr_1158 (coe v0) (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-L
d_inferElabV'45'RBinOp'45'L_3124 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RBinOp'45'L_3124 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_inferElabV'45'RBinOp'45'L_3124 v0 v2 v3 v4 v5 v6 v7 v8
du_inferElabV'45'RBinOp'45'L_3124 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.NumTable.T_NumView_8 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RBinOp'45'L_3124 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.NumTable.C_is'45'num_14 v8
        -> case coe v7 of
             C_success_98 v9 v10 v11 v12 v13
               -> coe
                    du_inferElabV'45'RBinOp'45'R_3078 (coe v0) (coe v1) (coe v8)
                    (coe v9) (coe v3) (coe v10) (coe v4) (coe v11)
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v5) (coe v12))
                    (coe v13)
                    (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v9))
             C_failure_100 v9
               -> coe
                    C_failure_100
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_112 (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.NumTable.C_not'45'num_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_110
                (coe
                   d_numErr_1158 (coe v0) (coe MAlonzo.Code.Once.Spec.Theory.C_int_8)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_3180 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RBinOp'45'aux_3180 v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_inferElabV'45'RBinOp'45'aux_3180 v0 v2 v5 v6
du_inferElabV'45'RBinOp'45'aux_3180 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Operator.T_BinOp_36 ->
  T_InferElabResult_82 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RBinOp'45'aux_3180 v0 v1 v2 v3
  = case coe v2 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe
             du_inferElabV'45'RBinOp'45'L_3124 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe MAlonzo.Code.Once.TypeCheck.NumTable.du_numView_24 (coe v4))
             (coe v3)
      C_failure_100 v4
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_110 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_3232 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux2_3232 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
                                  ~v9 v10
  = du_inferElabV'45'RLet'45'aux2_3232 v5 v6 v7 v8 v10
du_inferElabV'45'RLet'45'aux2_3232 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux2_3232 v0 v1 v2 v3 v4
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
d_inferElabV'45'RDestruct'45'join_3322 ::
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
d_inferElabV'45'RDestruct'45'join_3322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
                                       v23
  = du_inferElabV'45'RDestruct'45'join_3322
      v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_inferElabV'45'RDestruct'45'join_3322 ::
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
du_inferElabV'45'RDestruct'45'join_3322 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v5
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
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v10
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
d_given'45'case'45'join_3420 ::
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
d_given'45'case'45'join_3420 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16
  = du_given'45'case'45'join_3420
      v0 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_given'45'case'45'join_3420 ::
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
du_given'45'case'45'join_3420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13
  = case coe v13 of
      MAlonzo.Code.Once.Type.Join.C_joined_174 v14 v15
        -> coe
             C_success_160 (coe v14)
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v5)
                (coe v9))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_copair''_322 v5 v9
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
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
                   MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
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
d_inferElabV'45'RDestruct'45'auxR_3512 ::
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
d_inferElabV'45'RDestruct'45'auxR_3512 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7 v8 v9 v10 v11 ~v12 v13 v14 v15 v16 v17 ~v18 v19
  = du_inferElabV'45'RDestruct'45'auxR_3512
      v0 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17 v19
du_inferElabV'45'RDestruct'45'auxR_3512 ::
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
du_inferElabV'45'RDestruct'45'auxR_3512 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11
  = case coe v11 of
      C_success_98 v12 v13 v14 v15 v16
        -> case coe v13 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v18 v19
               -> coe
                    du_inferElabV'45'RDestruct'45'join_3322 (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v12) (coe v18) (coe v19) (coe v14) (coe v15) (coe v16)
                    (coe
                       MAlonzo.Code.Once.Type.Join.d_join'63'_638 (coe v0) (coe v6)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-word
d_inferElabV'45'RResolved'45'word_3594 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'word_3594 ~v0 ~v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'word_3594 v2 v3 v4
du_inferElabV'45'RResolved'45'word_3594 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  (AgdaAny -> T_InferElabResult_82) -> Bool -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'word_3594 v0 v1 v2
  = if coe v2
      then coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v0)))
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_3626 ::
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
d_inferElabV'45'RResolved'45'arrow'45'aux_3626 v0 v1 v2 ~v3 v4 v5
                                               v6 ~v7 v8 ~v9 v10 ~v11
  = du_inferElabV'45'RResolved'45'arrow'45'aux_3626
      v0 v1 v2 v4 v5 v6 v8 v10
du_inferElabV'45'RResolved'45'arrow'45'aux_3626 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Base_84 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'arrow'45'aux_3626 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_inferElabV'45'RResolved'45'word_3594 (coe v2)
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
                               MAlonzo.Code.Once.Surface.Syntax.C_sigOp_236
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
d_inferElabV'45'RResolved'45'value'45'aux_3686 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'value'45'aux_3686 v0 v1 v2 ~v3 v4 ~v5
                                               v6 ~v7
  = du_inferElabV'45'RResolved'45'value'45'aux_3686 v0 v1 v2 v4 v6
du_inferElabV'45'RResolved'45'value'45'aux_3686 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'value'45'aux_3686 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_inferElabV'45'RResolved'45'word_3594 (coe v2)
             (coe
                (\ v6 ->
                   coe
                     C_success_98
                     (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v3))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                        (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
                     (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_236 v3 v2 v5)
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
d_inferElabV'45'RResolved'45'def_3718 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'def_3718 v0 v1 v2 ~v3
  = du_inferElabV'45'RResolved'45'def_3718 v0 v1 v2
du_inferElabV'45'RResolved'45'def_3718 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_InferElabResult_82
du_inferElabV'45'RResolved'45'def_3718 v0 v1 v2
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
                              du_inferElabV'45'RResolved'45'own'45'aux_3728 (coe v0) (coe v1)
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v1))
                                 (coe v5))
                       _ -> coe v4
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-own-aux
d_inferElabV'45'RResolved'45'own'45'aux_3728 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'own'45'aux_3728 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'own'45'aux_3728 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'own'45'aux_3728 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'own'45'aux_3728 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_success_98
             (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4))
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_244 v2)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_inferElabV'45'RVar'45'poly'45'aux_2114 (coe v0) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_3738 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'aux_3738 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RResolved'45'aux_3738 v0 v1 v2 v4
du_inferElabV'45'RResolved'45'aux_3738 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_InferElabResult_82
du_inferElabV'45'RResolved'45'aux_3738 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_3686 (coe v0) (coe v1)
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
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_3626 (coe v0)
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
             du_inferElabV'45'RResolved'45'def_3718 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_3812 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RVar'45'lookup'45'aux_3812 ~v0 ~v1 v2 v3 ~v4
  = du_inferElabV'45'RVar'45'lookup'45'aux_3812 v2 v3
du_inferElabV'45'RVar'45'lookup'45'aux_3812 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_InferElabResult_82
du_inferElabV'45'RVar'45'lookup'45'aux_3812 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           C_success_98 (coe v3) (coe v5)
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_416 (coe v6))
                           (coe (0 :: Integer)) (coe (0 :: Integer))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_20 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_3840 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_3840 v0 v1 v2
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
                                               du_withUnit_320 (coe C_failure_128 (coe v3)) (coe v8)
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
                                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                                          (coe MAlonzo.Code.Once.IR.C_id_20))
                                                       (coe (0 :: Integer)) (coe (0 :: Integer)))))
                                     else coe seq (coe v11) (coe C_failure_128 (coe v3))
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
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_3932 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_3932 v0 v1 v2
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
                                                      du_withUnit_320 (coe C_failure_128 (coe v3))
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
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_fst_42))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe seq (coe v13) (coe C_failure_128 (coe v3))
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
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4068 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4068 v0 v1 v2
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
                                                      du_withUnit_320 (coe C_failure_128 (coe v3))
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
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_snd_48))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe seq (coe v13) (coe C_failure_128 (coe v3))
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
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204 ~v0
                                                               v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204 v0
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
                                  du_withUnit_320 (coe C_failure_128 (coe v2)) (coe v7)
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
                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
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
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308 ~v0
                                                              v1 v2 v3
  = du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308
      v1 v2 v3
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308 v0
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
                                  du_withUnit_320 (coe C_failure_128 (coe v2)) (coe v7)
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
                                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
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
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_4412 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_4412 v0 v1 v2
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
                                                      du_withUnit_320 (coe C_failure_128 (coe v3))
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
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_inl_54))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe seq (coe v13) (coe C_failure_128 (coe v3))
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
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_4548 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_4548 v0 v1 v2
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
                                                      du_withUnit_320 (coe C_failure_128 (coe v3))
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
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_inr_60))
                                                              (coe (0 :: Integer))
                                                              (coe (0 :: Integer)))))
                                            else coe seq (coe v13) (coe C_failure_128 (coe v3))
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
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_4682 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_4682 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_3840 (coe v0)
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("id" :: Data.Text.Text)) (coe d_schema'45'id_2138) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_4702 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_4702 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_3932 (coe v0)
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("fst" :: Data.Text.Text)) (coe d_schema'45'fst_2140)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_4722 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_4722 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_4068 (coe v0)
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("snd" :: Data.Text.Text)) (coe d_schema'45'snd_2142)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_4742 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_4742 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             du_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_4204
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("terminal" :: Data.Text.Text))
                (coe d_schema'45'terminal_2144) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_4762 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_4762 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             du_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_4308
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("initial" :: Data.Text.Text)) (coe d_schema'45'initial_2146)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_4782 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_4782 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_4412 (coe v0)
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("inl" :: Data.Text.Text)) (coe d_schema'45'inl_2148)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_4802 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_4802 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> coe du_embedOrSubsume_540 (coe v0) (coe v2) (coe v3)
      C_failure_100 v4
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_4548 (coe v0)
             (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_NoInstance_94 (coe v0)
                (coe ("inr" :: Data.Text.Text)) (coe d_schema'45'inr_2150)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_4822 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  T_InferElabResult_82
d_inferElabV'45'RResolved'45'dispatch_4822 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_GeneratorInInferMode_46
                (coe ("id" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_GeneratorInInferMode_46
                (coe ("fst" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_GeneratorInInferMode_46
                (coe ("snd" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_GeneratorInInferMode_46
                (coe ("terminal" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_42)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_38)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_40)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'toFloat_658
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
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274
                MAlonzo.Code.Once.Surface.Numeric.d_toFloatIR_6)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_662 v5
        -> coe
             du_inferElabV'45'RResolved'45'aux_3738 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_sig_140 (coe v1))
                (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-other
d_checkElabV'45'RResolved'45'other_4870 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RResolved'45'other_4870 v0 v1 v2 v3 v4
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
                                  du_checkElabV'45'RVar'45'poly'45'check'45'aux_1986 (coe v0)
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
d_checkElabV'45'RResolved'45'dispatch_4908 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_640 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RResolved'45'dispatch_4908 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_642
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_4682 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_644
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_4702 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_646
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_4722 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_648
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_4742 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_650
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_4762 (coe v0)
             (coe v1) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_652
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_4782 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_654
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_4802 (coe v0) (coe v1)
             (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_656
        -> coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'toFloat_658
        -> coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_662 v7
        -> coe
             d_checkElabV'45'RResolved'45'other_4870 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 v0 ~v1 ~v2 v3 v4
  = du_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 v0 v3 v4
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_InferElabResult_82 -> T_CheckElabResult_110
du_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 v0 v1 v2
  = coe du_embedOrSubsume_540 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-at
d_inferElabV'45'RFloat'45'at_5008 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
d_inferElabV'45'RFloat'45'at_5008 ~v0 v1 v2 v3 v4 v5 v6
  = du_inferElabV'45'RFloat'45'at_5008 v1 v2 v3 v4 v5 v6
du_inferElabV'45'RFloat'45'at_5008 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_InferElabResult_82
du_inferElabV'45'RFloat'45'at_5008 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       C_failure_100
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_NegativeZeroLiteral_108))
             else coe
                    seq (coe v7)
                    (coe
                       C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                       (coe
                          MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                          (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_202
                          (MAlonzo.Code.Once.Spec.Surface.Syntax.d_signedDecimal_74
                             (coe v1) (coe v2) (coe v3) (coe v4)))
                       (coe (0 :: Integer)) (coe (0 :: Integer)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_5042 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> T_InferElabResult_82
d_inferElabV'45'RFloat'45'aux_5042 ~v0 v1 v2 v3 v4 v5
  = du_inferElabV'45'RFloat'45'aux_5042 v1 v2 v3 v4 v5
du_inferElabV'45'RFloat'45'aux_5042 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> Integer -> T_InferElabResult_82
du_inferElabV'45'RFloat'45'aux_5042 v0 v1 v2 v3 v4
  = coe
      du_inferElabV'45'RFloat'45'at_5008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.TypeCheck.NumTable.d_negZero'63'_92 (coe v1)
         (coe v2) (coe v3))
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-at
d_checkElabV'45'RFloat'45'at_5068 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CheckElabResult_110
d_checkElabV'45'RFloat'45'at_5068 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       C_failure_128
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_NegativeZeroLiteral_108))
             else coe
                    seq (coe v9)
                    (let v10
                           = MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                               (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v6) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then case coe v12 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                          -> coe
                                               C_success_126
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Scope.d_size_130
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
                                                  (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) v13
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                                     (MAlonzo.Code.Once.Spec.Surface.Syntax.d_signedDecimal_74
                                                        (coe v2) (coe v3) (coe v4) (coe v5))))
                                               (coe (0 :: Integer)) (coe (0 :: Integer))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v12)
                                        (coe
                                           C_failure_128
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                              (coe v0) (coe v6)
                                              (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_5138 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'RFloat'45'aux_5138 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_checkElabV'45'RFloat'45'at_5068 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.NumTable.d_negZero'63'_92 (coe v2)
         (coe v3) (coe v4))
-- Once.TypeCheck.Elaborate.checkPairOn
d_checkPairOn_5162 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_PairTarget_146 ->
  T_CheckElabResult_110
d_checkPairOn_5162 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_pair'45'at_158
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v13 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
                             -> let v17
                                      = d_checkElab_5440
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
                                                = d_checkElab_5440
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
                                                         MAlonzo.Code.Once.Surface.Syntax.C_fork''_340
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
d_checkPairLit_5176 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkPairLit_5176 v0 v1 v2 v3 v4 v5
  = let v6 = d_checkElab_5440 (coe v0) (coe v1) (coe v2) (coe v4) in
    coe
      (case coe v6 of
         C_success_126 v7 v8 v9 v10
           -> let v11
                    = d_checkElab_5440 (coe v0) (coe v1) (coe v3) (coe v5) in
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
d_checkCaseOn_5188 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CaseTarget_180 ->
  T_CheckElabResult_110
d_checkCaseOn_5188 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_case'45'at_192
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                      -> case coe v11 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v15 v16
                             -> coe
                                  d_checkCaseGo_5206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                                  (coe v14) (coe v12) (coe v16)
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
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_5206 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_CheckElabResult_110
d_checkCaseGo_5206 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_checkElab_5440
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
                    = d_checkElab_5440
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
                             MAlonzo.Code.Once.Surface.Syntax.C_copair''_322 v9 v14 v10 v15)
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
d_checkComposeOn_5218 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_ArrowTarget_214 ->
  T_CheckElabResult_110
d_checkComposeOn_5218 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'at_224
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                      -> coe
                           d_checkCompose'45'g_5260 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v9) (coe v11) (coe v13)
                           (coe
                              d_elabGiven_5230 (coe v0) (coe v1) (coe v3) (coe v9) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_arrow'45'other_228
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("compose" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.elabGiven
d_elabGiven_5230 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> T_GivenElabResult_140
d_elabGiven_5230 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_given'45'infer_264 (coe v0) (coe v3) (coe v4)
              (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v6
           -> coe
                d_elabGivenLeaf_2162 (coe v0) (coe v1) (coe v6) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v2))
                (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v6 v7
           -> coe
                d_elabGivenApp_5244 (coe v0) (coe v1) (coe v6) (coe v7) (coe v3)
                (coe v4)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v6))
                (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v6 v7
           -> let v8
                    = d_inferElab_5430
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
                                     = d_decideLeq_1242
                                         (coe v15) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) in
                               coe
                                 (case coe v17 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                      -> coe
                                           du_withUnit_320
                                           (coe
                                              C_failure_162
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                 (coe ("lambda" :: Data.Text.Text))))
                                           (coe v4)
                                           (coe
                                              (\ v19 ->
                                                 coe
                                                   C_success_160 (coe v9) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v15
                                                      v11)
                                                   (coe addInt (coe (1 :: Integer)) (coe v12))
                                                   (coe v13)))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           C_failure_162
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_80
                                              (coe v6) (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v15))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_failure_100 v9 -> coe C_failure_162 (coe v9)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v5)
-- Once.TypeCheck.Elaborate.elabGivenApp
d_elabGivenApp_5244 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82 -> T_GivenElabResult_140
d_elabGivenApp_5244 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe du_given'45'infer_264 (coe v0) (coe v4) (coe v5) (coe v7) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
           -> let v9
                    = coe
                        C_failure_162
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                    du_given'45'cata_434 (coe v0) (coe v1) (coe v10) (coe v5)
                                    (coe v12) (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> coe
                                    C_failure_162
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                       (coe ("cata" :: Data.Text.Text)))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> coe v9)
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v10 v11
                  -> let v12
                           = d_elabGiven_5230 (coe v0) (coe v1) (coe v11) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          C_success_160 v13 v14 v15 v16 v17
                            -> let v18
                                     = d_elabGiven_5230
                                         (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                               coe
                                 (case coe v18 of
                                    C_success_160 v19 v20 v21 v22 v23
                                      -> coe
                                           C_success_160
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v13)
                                              (coe v19))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v14) (coe v20))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_fork''_340 v14 v20
                                              v15 v21)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16)
                                                 (coe v22)))
                                           (coe v23)
                                    C_failure_162 v19 -> coe v18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failure_162 v13 -> coe v12
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v10 v11
                  -> let v12
                           = d_elabGiven_5230 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) in
                     coe
                       (case coe v12 of
                          C_success_160 v13 v14 v15 v16 v17
                            -> let v18
                                     = d_elabGiven_5230
                                         (coe v0) (coe v1) (coe v11) (coe v13) (coe v5) in
                               coe
                                 (case coe v18 of
                                    C_success_160 v19 v20 v21 v22 v23
                                      -> coe
                                           C_success_160 (coe v19)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v20)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v14)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_comp''_304 v20 v14
                                              v13 v21 v15)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v22)
                                                 (coe v16)))
                                           (coe v23)
                                    C_failure_162 v19 -> coe v18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_failure_162 v13 -> coe v12
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v8
         MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v10 v11
                  -> let v12
                           = coe
                               C_failure_162
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                  (coe ("case" :: Data.Text.Text))) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
                            -> let v15
                                     = d_elabGiven_5230
                                         (coe v0) (coe v1) (coe v11) (coe v13) (coe v5) in
                               coe
                                 (case coe v15 of
                                    C_success_160 v16 v17 v18 v19 v20
                                      -> let v21
                                               = d_elabGiven_5230
                                                   (coe v0) (coe v1) (coe v3) (coe v14) (coe v5) in
                                         coe
                                           (case coe v21 of
                                              C_success_160 v22 v23 v24 v25 v26
                                                -> coe
                                                     du_given'45'case'45'join_3420 (coe v0)
                                                     (coe v13) (coe v14) (coe v5) (coe v16)
                                                     (coe v17) (coe v18) (coe v19) (coe v22)
                                                     (coe v23) (coe v24) (coe v25) (coe v26)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.Join.d_join'63'_638
                                                        (coe v0) (coe v16) (coe v22))
                                              C_failure_162 v22 -> coe v21
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_162 v16 -> coe v15
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v12)
                _ -> coe v8
         _ -> coe v8)
-- Once.TypeCheck.Elaborate.checkCompose-g
d_checkCompose'45'g_5260 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_GivenElabResult_140 -> T_CheckElabResult_110
d_checkCompose'45'g_5260 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_160 v8 v9 v10 v11 v12
        -> let v13
                 = d_checkElab_5440
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
                          MAlonzo.Code.Once.Surface.Syntax.C_comp''_304 v14 v9 v8 v15 v10)
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v16) (coe v11)))
                       (coe v17)
                C_failure_128 v14
                  -> coe
                       d_checkCompose'45'f_5276 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v14))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_162 v8
        -> coe
             d_checkCompose'45'f_5276 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6)
             (coe
                du_determinedErr_2128
                (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCompose-f
d_checkCompose'45'f_5276 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_18 ->
  T_CheckElabResult_110
d_checkCompose'45'f_5276 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = d_inferElab_5430 (coe v0) (coe v1) (coe v2) in
    coe
      (let v9
             = coe
                 C_failure_128
                 (coe
                    MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_ComposeMiddleUndetermined_96)
                    v7) in
       coe
         (case coe v8 of
            C_success_98 v10 v11 v12 v13 v14
              -> case coe v10 of
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
                     -> case coe v16 of
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v18 v19
                            -> case coe v18 of
                                 MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                   -> let v20
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
                                                   (coe v0) (coe v15) (coe v15))
                                                (coe
                                                   MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                                                   (coe v0) (coe v17) (coe v5))
                                                (coe
                                                   MAlonzo.Code.Once.Type.SubDecide.d__'8849'π'63'__10
                                                   (coe v19) (coe v6)) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                             -> if coe v21
                                                  then case coe v22 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                           -> let v24
                                                                    = d_checkElab_5440
                                                                        (coe v0) (coe v1) (coe v3)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                           (coe v4)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                              (coe v18) (coe v6))
                                                                           (coe v15)) in
                                                              coe
                                                                (case coe v24 of
                                                                   C_success_126 v25 v26 v27 v28
                                                                     -> coe
                                                                          C_success_126
                                                                          (coe
                                                                             MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                                                             (coe v11)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                                                (coe v18)
                                                                                (coe v25)))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Syntax.C_comp''_304
                                                                             v11 v25 v15
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.C_coerce_228
                                                                                v10 v23 v12)
                                                                             v26)
                                                                          (coe
                                                                             addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                (coe v13)
                                                                                (coe v27)))
                                                                          (coe v28)
                                                                   C_failure_128 v25 -> coe v24
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  else coe
                                                         seq (coe v22)
                                                         (coe
                                                            C_failure_128
                                                            (coe
                                                               MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
                                                                  (coe v0)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                                     (coe v15)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                                        (coe v18) (coe v6))
                                                                     (coe v5))
                                                                  (coe v10))
                                                               v7))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> coe v9
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v9
            _ -> coe v9))
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_5286 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkCurry_5286 v0 v1 v2 v3
  = coe
      d_checkCurryOn_5296 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_curryTarget_132 (coe v3))
-- Once.TypeCheck.Elaborate.checkCurryOn
d_checkCurryOn_5296 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CurryTarget_108 ->
  T_CheckElabResult_110
d_checkCurryOn_5296 v0 v1 v2 v3 v4
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
                                             = d_checkElab_5440
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
                                                   du_withUnit_320
                                                   (coe
                                                      C_failure_128
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                         (coe ("curry" :: Data.Text.Text))))
                                                   (coe v14)
                                                   (coe
                                                      (\ v25 ->
                                                         coe
                                                           C_success_126 (coe v21)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_curry''_358
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("curry" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferOut
d_inferOut_5304 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferOut_5304 v0 v1 v2
  = coe
      du_inferOutOn_2378 (coe v0) (coe v1)
      (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_5314 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkIn_5314 v0 v1 v2 v3
  = coe
      d_checkInOn_5324 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_inTarget_102 (coe v3))
-- Once.TypeCheck.Elaborate.checkInOn
d_checkInOn_5324 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_InTarget_86 ->
  T_CheckElabResult_110
d_checkInOn_5324 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'at_92
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    du_checkInGo_5336 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Functor.Decide.du_wfFun'63'_468
                       (coe MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.TargetView.C_in'45'other_96
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("In" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_5336 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkInGo_5336 v0 v1 v2 v3 v4 ~v5
  = du_checkInGo_5336 v0 v1 v2 v3 v4
du_checkInGo_5336 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkInGo_5336 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> let v6
                 = d_checkElab_5440
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
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v7
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("In" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_5346 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkCata_5346 v0 v1 v2 v3
  = coe
      d_checkCataOn_5356 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_cataTarget_28 (coe v3))
-- Once.TypeCheck.Elaborate.checkCataOn
d_checkCataOn_5356 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_CataTarget_8 ->
  T_CheckElabResult_110
d_checkCataOn_5356 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_cata'45'at_18
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v12 v13
                             -> coe
                                  du_checkCataGo_5372 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10)
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
d_checkCataGo_5372 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkCataGo_5372 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_checkCataGo_5372 v0 v1 v2 v3 v4 v5 v6
du_checkCataGo_5372 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkCataGo_5372 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = d_checkElab_5440
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
                       du_withUnit_320
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_374 v9
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v7 v10)
                               (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)))
                C_failure_128 v9 -> coe v8
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAna
d_checkAna_5382 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkAna_5382 v0 v1 v2 v3
  = coe
      d_checkAnaOn_5392 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.TargetView.du_anaTarget_66 (coe v3))
-- Once.TypeCheck.Elaborate.checkAnaOn
d_checkAnaOn_5392 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.TargetView.T_AnaTarget_38 ->
  T_CheckElabResult_110
d_checkAnaOn_5392 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.TargetView.C_loop'45'at_46
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> coe
                    du_checkLoop_5422
                    (coe
                       d_checkElab_5440 (coe v0) (coe v1) (coe v2)
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
                                  du_checkAnaGo_5410 (coe v0) (coe v1) (coe v2) (coe v15) (coe v10)
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
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkAnaGo
d_checkAnaGo_5410 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkAnaGo_5410 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9
  = du_checkAnaGo_5410 v0 v1 v2 v3 v4 v5 v6 v8
du_checkAnaGo_5410 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  T_CheckElabResult_110
du_checkAnaGo_5410 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> let v9
                 = d_checkElab_5440
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
                       du_withUnit_320
                       (coe
                          C_failure_128
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_392 v10
                                  (MAlonzo.Code.Once.TypeCheck.Scope.d_kinds_142 (coe v1)) v8 v11)
                               (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)))
                C_failure_128 v10 -> coe v9
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_failure_128
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("ana" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkLoop
d_checkLoop_5422 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_CheckElabResult_110 -> T_CheckElabResult_110
d_checkLoop_5422 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_checkLoop_5422 v5
du_checkLoop_5422 :: T_CheckElabResult_110 -> T_CheckElabResult_110
du_checkLoop_5422 v0
  = case coe v0 of
      C_success_126 v1 v2 v3 v4
        -> coe
             C_success_126
             (coe
                MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_loop_404 v1 v2)
             (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)
      C_failure_128 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_5430 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferElab_5430 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v3
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_3812 (coe v3)
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
             d_inferElabV'45'RResolved'45'dispatch_4822 (coe v0) (coe v1)
             (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_694 (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v3 v4
        -> coe
             du_inferElabV'45'RApp'45'dispatch_5540 (coe v0) (coe v1) (coe v3)
             (coe v4)
             (coe
                MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v3 v4
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_34)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_56 v3 v4 v5
        -> coe
             du_inferElabV'45'RLet'45'aux_5472 (coe v0) (coe v1) (coe v3)
             (coe v5) (coe d_inferElab_5430 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v3 v4
        -> coe
             du_inferElabV'45'RPair'45'aux_2788
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_60 v3 v4 v5 v6 v7
        -> coe
             du_inferElabV'45'RDestruct'45'aux_5488 (coe v0) (coe v1) (coe v4)
             (coe v5) (coe v6) (coe v7)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_62
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_64 v3
        -> coe
             C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe
                MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v3)
             (coe (0 :: Integer)) (coe (0 :: Integer))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_66 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RFloat'45'aux_5042 (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_68 v3 v4
        -> coe
             du_inferElabV'45'RAnnot'45'aux_2840 (coe v0) (coe v4)
             (coe
                d_checkElab_5440 (coe v0) (coe v1) (coe v3)
                (coe MAlonzo.Code.Once.Type.Core.d_wk'8320'_12 (coe v0) (coe v4)))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_70 v3 v4 v5
        -> coe
             du_inferElabV'45'RBinOp'45'aux_3180 (coe v0) (coe v3)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v4))
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v3
        -> coe
             du_inferElabV'45'RNeg'45'aux_2940 (coe v0)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_5440 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab_5440 v0 v1 v2 v3
  = coe du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Elaborate.checkElab-wf
d_checkElab'45'wf_5450 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElab'45'wf_5450 v0 v1 ~v2 v3 v4
  = du_checkElab'45'wf_5450 v0 v1 v3 v4
du_checkElab'45'wf_5450 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
du_checkElab'45'wf_5450 v0 v1 v2 v3
  = let v4
          = coe
              du_embedOrSubsume_540 (coe v0) (coe v3)
              (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_46 v5
           -> let v6
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_3812 (coe v5)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal'45'go_170 (coe v0)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1))
                           (coe v5)
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_named_132 (coe v1))
                           (coe MAlonzo.Code.Once.TypeCheck.Scope.d_debruijn_134 (coe v1))) in
              coe
                (case coe v6 of
                   C_success_98 v7 v8 v9 v10 v11
                     -> coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v6)
                   C_failure_100 v7
                     -> coe
                          du_checkElabV'45'RVar'45'bbc'45'other'45'aux_4986 (coe v0) (coe v3)
                          (coe v6)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_50 v5
           -> coe
                d_checkElabV'45'RResolved'45'dispatch_4908 (coe v0) (coe v1)
                (coe v5) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_694 (coe v5))
                (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v5 v6
           -> coe
                du_checkElabV'45'RApp'45'dispatch_5554 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                   (coe v5))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_54 v5 v6
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
                                     = d_checkElab_5440
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
                                             -> let v21 = d_decideLeq_1242 (coe v19) (coe v11) in
                                                coe
                                                  (case coe v21 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                       -> coe
                                                            du_withUnit_320
                                                            (coe
                                                               C_failure_128
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                               MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_80
                                                               (coe v5) (coe v11) (coe v19))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    C_failure_128 v14 -> coe v13
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v7)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_58 v5 v6
           -> coe
                d_checkElabV'45'RPair'45'aux_5586 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v3) (coe du_classifyRPairTarget_60 (coe v3))
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_64 v5
           -> coe
                d_checkElabV'45'RInt'45'aux_5574 (coe v0) (coe v1) (coe v5)
                (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_66 v5 v6 v7 v8
           -> coe
                d_checkElabV'45'RFloat'45'aux_5138 (coe v0) (coe v1) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v3)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_72 v5
           -> coe
                du_embedOrSubsume_540 (coe v0) (coe v3)
                (coe
                   du_inferElabV'45'RNeg'45'aux_2940 (coe v0)
                   (coe d_inferElab_5430 (coe v0) (coe v1) (coe v5)))
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_5460 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'other_5460 v0 v1 v2 v3
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_5528 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHead_580 (coe v2))
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_5472 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RLet'45'aux_5472 v0 v1 v2 ~v3 v4 v5
  = du_inferElabV'45'RLet'45'aux_5472 v0 v1 v2 v4 v5
du_inferElabV'45'RLet'45'aux_5472 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RLet'45'aux_5472 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_98 v5 v6 v7 v8 v9
        -> coe
             du_inferElabV'45'RLet'45'aux2_3232 (coe v5) (coe v6) (coe v7)
             (coe v8)
             (coe
                d_inferElab_5430 (coe v0)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                   (coe v2) (coe v5))
                (coe v3))
      C_failure_100 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_5488 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferElabV'45'RDestruct'45'aux_5488 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_inferElabV'45'RDestruct'45'aux_5488 v0 v1 v3 v4 v5 v6 v7
du_inferElabV'45'RDestruct'45'aux_5488 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'aux_5488 v0 v1 v2 v3 v4 v5 v6
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
                    du_inferElabV'45'RDestruct'45'auxL_5516 (coe v0) (coe v1) (coe v4)
                    (coe v5) (coe v12) (coe v13) (coe v8) (coe v9) (coe v10)
                    (coe
                       d_inferElab_5430 (coe v0)
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
d_inferElabV'45'RDestruct'45'auxL_5516 ::
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
d_inferElabV'45'RDestruct'45'auxL_5516 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7
                                       v8 v9 v10 v11 ~v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_5516
      v0 v1 v5 v6 v7 v8 v9 v10 v11 v13
du_inferElabV'45'RDestruct'45'auxL_5516 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> T_InferElabResult_82 -> T_InferElabResult_82
du_inferElabV'45'RDestruct'45'auxL_5516 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      C_success_98 v10 v11 v12 v13 v14
        -> case coe v11 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v16 v17
               -> coe
                    du_inferElabV'45'RDestruct'45'auxR_3512 (coe v0) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8) (coe v10) (coe v16) (coe v17) (coe v12)
                    (coe v13)
                    (coe
                       d_inferElab_5430 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Scope.du_extendNamedCtx_148 (coe v1)
                          (coe v2) (coe v5))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_100 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_5528 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Scope.T_PolyBuiltinApp_270 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'other'45'aux_5528 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'other'45'aux_5528 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'other'45'aux_5528 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Scope.T_PolyBuiltinApp_270 ->
  T_InferElabResult_82
du_inferElabV'45'RApp'45'other'45'aux_5528 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe
                   ("unreachable: ahv-other \8658 classifyAppHead nothing"
                    ::
                    Data.Text.Text)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v5 = d_inferElab_5430 (coe v0) (coe v1) (coe v2) in
           coe
             (case coe v5 of
                C_success_98 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v11
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Unit_18
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Void_20
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
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
                                                           du_checkElab'45'wf_5450 (coe v0) (coe v1)
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
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                             (coe v0) (coe v6))
                                                   MAlonzo.Code.Once.Spec.Grade.C_One_10
                                                     -> coe
                                                          C_failure_100
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                             (coe v0) (coe v6))
                                                   MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                                     -> let v17
                                                              = coe
                                                                  du_checkElab'45'wf_5450 (coe v0)
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
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                      (coe v0) (coe v6))
                                            MAlonzo.Code.Once.Spec.Grade.C_One_10
                                              -> coe
                                                   C_failure_100
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                                      (coe v0) (coe v6))
                                            MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                              -> let v16
                                                       = coe
                                                           du_checkElab'45'wf_5450 (coe v0) (coe v1)
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
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v11 v12
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72 (coe v0)
                                 (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Int_32
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                 (coe (0 :: Integer)) (coe v6))
                       MAlonzo.Code.Once.Spec.Type.C_Float_34
                         -> coe
                              C_failure_100
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_72
                                 (coe (0 :: Integer)) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_100 v6
                  -> coe
                       du_inferSpine_5564 (coe v0) (coe v1) (coe v2)
                       (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_5540 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82
d_inferElabV'45'RApp'45'dispatch_5540 v0 v1 v2 v3 v4 ~v5
  = du_inferElabV'45'RApp'45'dispatch_5540 v0 v1 v2 v3 v4
du_inferElabV'45'RApp'45'dispatch_5540 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_InferElabResult_82
du_inferElabV'45'RApp'45'dispatch_5540 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
        -> let v5 = d_inferElab_5430 (coe v0) (coe v1) (coe v3) in
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
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v7 v6
                          (coe MAlonzo.Code.Once.IR.C_id_20) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_100 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
        -> coe
             du_inferFstOn_2452 (coe v1)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
        -> coe
             du_inferSndOn_2526 (coe v1)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
        -> let v5 = d_inferElab_5430 (coe v0) (coe v1) (coe v3) in
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
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v7 v6
                          (coe MAlonzo.Code.Once.IR.C_terminal_72) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_100 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inl_314
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_38)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inr_316
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_40)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
        -> coe
             C_failure_100
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_42)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'curry_320
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("curry" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'apply_322
        -> coe
             du_inferApplyOn_2758 (coe v0) (coe v1)
             (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'In_324
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("In" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("cata" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'ana_328
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("ana" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'Out_330
        -> coe d_inferOut_5304 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("pair" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("compose" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
        -> coe
             C_failure_100
             (coe
                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                (coe ("case" :: Data.Text.Text)))
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'other_346
        -> coe
             d_inferElabV'45'RApp'45'other_5460 (coe v0) (coe v1) (coe v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_5554 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_110
d_checkElabV'45'RApp'45'dispatch_5554 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkElabV'45'RApp'45'dispatch_5554 v0 v1 v2 v3 v4 v5
du_checkElabV'45'RApp'45'dispatch_5554 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_AppHeadView_304 ->
  T_CheckElabResult_110
du_checkElabV'45'RApp'45'dispatch_5554 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'id_306
        -> let v6 = d_inferElab_5430 (coe v0) (coe v1) (coe v3) in
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
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_id_20) v9)
                               (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11) in
                     coe (coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v12))
                C_failure_100 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v8 -> coe C_failure_128 (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'fst_308
        -> let v6
                 = coe
                     du_inferFstOn_2452 (coe v1)
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'snd_310
        -> let v6
                 = coe
                     du_inferSndOn_2526 (coe v1)
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'terminal_312
        -> let v6 = d_inferElab_5430 (coe v0) (coe v1) (coe v3) in
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
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_terminal_72) v9)
                               (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11) in
                     coe (coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v12))
                C_failure_100 v7
                  -> case coe v6 of
                       C_success_98 v8 v9 v10 v11 v12
                         -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                       C_failure_100 v8 -> coe C_failure_128 (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inl_314
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v3) (coe v6) in
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
                                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v9 v6
                                 (coe MAlonzo.Code.Once.IR.C_inl_54) v10)
                              (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                       C_failure_128 v9 -> coe v8
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_48)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'inr_316
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C_var_16 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_Unit_18
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_Void_20
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> let v8
                        = coe
                            du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v3) (coe v7) in
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
                                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v9 v7
                                 (coe MAlonzo.Code.Once.IR.C_inr_60) v10)
                              (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12)
                       C_failure_128 v9 -> coe v8
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v6 v7 v8
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v6 v7
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_Int_32
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             MAlonzo.Code.Once.Spec.Type.C_Float_34
               -> coe
                    C_failure_128
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_50)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'initial_318
        -> let v6
                 = coe
                     du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v3)
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
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v7
                          (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                          (coe MAlonzo.Code.Once.IR.C_initial_76) v8)
                       (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                C_failure_128 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'curry_320
        -> coe d_checkCurry_5286 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'apply_322
        -> let v6
                 = coe
                     du_inferApplyOn_2758 (coe v0) (coe v1)
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'In_324
        -> coe d_checkIn_5314 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'cata_326
        -> coe d_checkCata_5346 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'ana_328
        -> coe d_checkAna_5382 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'Out_330
        -> let v6
                 = coe
                     du_inferOutOn_2378 (coe v0) (coe v1)
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v6 of
                C_success_98 v7 v8 v9 v10 v11
                  -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v6)
                C_failure_100 v7 -> coe C_failure_128 (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'pair'45'applied_334
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v7 v8
               -> coe
                    d_checkPairOn_5162 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_pairTarget_168 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'compose'45'applied_338
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v7 v8
               -> coe
                    d_checkComposeOn_5218 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_arrowTarget_234 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'case'45'applied_342
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_52 v7 v8
               -> coe
                    d_checkCaseOn_5188 (coe v0) (coe v1) (coe v8) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.TargetView.du_caseTarget_202 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Scope.C_ahv'45'other_346
        -> let v7
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_5540 (coe v0) (coe v1) (coe v2)
                     (coe v3)
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
                        (coe v2)) in
           coe
             (case coe v7 of
                C_success_98 v8 v9 v10 v11 v12
                  -> coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v7)
                C_failure_100 v8 -> coe C_failure_128 (coe v8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferSpine
d_inferSpine_5564 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferElabResult_82 -> T_InferElabResult_82
d_inferSpine_5564 v0 v1 v2 ~v3 ~v4 v5
  = du_inferSpine_5564 v0 v1 v2 v5
du_inferSpine_5564 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82 -> T_InferElabResult_82
du_inferSpine_5564 v0 v1 v2 v3
  = case coe v3 of
      C_success_98 v4 v5 v6 v7 v8
        -> let v9
                 = d_elabGiven_5230
                     (coe v0) (coe v1) (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Spec.Grade.C_fin_42
                        (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)) in
           coe
             (case coe v9 of
                C_success_160 v10 v11 v12 v13 v14
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
                C_failure_162 v10 -> coe C_failure_100 (coe v10)
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_100 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_5574 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkElabV'45'RInt'45'aux_5574 v0 v1 v2 v3
  = let v4
          = coe
              C_success_98 (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
              (coe
                 MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44
                 (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1)))
              (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v2)
              (coe (0 :: Integer)) (coe (0 :: Integer)) in
    coe (coe du_embedOrSubsume_540 (coe v0) (coe v3) (coe v4))
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_5586 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_RPairTarget_32 -> T_CheckElabResult_110
d_checkElabV'45'RPair'45'aux_5586 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_rpt'45'prod_40
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v8 v9
               -> coe
                    d_checkPairLit_5176 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
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
        -> let v7
                 = coe
                     du_inferElabV'45'RPair'45'aux_2788
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2))
                     (coe d_inferElab_5430 (coe v0) (coe v1) (coe v3)) in
           coe (coe du_embedOrSubsume_540 (coe v0) (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_8928 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CheckElabResult_110
d_checkApply_8928 v0 v1 v2 v3
  = let v4 = d_inferElab_5430 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v4 of
         C_success_98 v5 v6 v7 v8 v9
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Type.C_var_16 v10
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Unit_18
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Void_20
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v10 v11
                  -> case coe v10 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v12
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Unit_18
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Void_20
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                         (coe ("apply" :: Data.Text.Text))))
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                         (coe ("apply" :: Data.Text.Text))))
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
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
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286
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
                                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_66
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
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                                                    (coe
                                                                                       ("apply"
                                                                                        ::
                                                                                        Data.Text.Text))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                                     -> coe
                                                          C_failure_128
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                             (coe ("apply" :: Data.Text.Text)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                              -> coe
                                                   C_failure_128
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                      (coe ("apply" :: Data.Text.Text)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v12
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v12 v13
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Int_32
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       MAlonzo.Code.Once.Spec.Type.C_Float_34
                         -> coe
                              C_failure_128
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                 (coe ("apply" :: Data.Text.Text)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v10 v11
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v10 v11 v12
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_μ_28 v10
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Int_32
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                MAlonzo.Code.Once.Spec.Type.C_Float_34
                  -> coe
                       C_failure_128
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                          (coe ("apply" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError
         C_failure_100 v5 -> coe C_failure_128 (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_9188 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_44 ->
  T_InferElabResult_82
d_inferElab'45'RApp'45'other_9188 v0 v1 v2 v3
  = let v4
          = coe
              du_asFun_1012 (coe v0)
              (coe d_inferElab_5430 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v4 of
         C_isFun_990 v5 v6 v7 v8 v9 v10 v11
           -> let v12
                    = coe
                        du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v3) (coe v5) in
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
         C_isEff_1002 v5 v6 v7 v8 v9 v10 v11 v12
           -> let v13
                    = coe
                        du_checkElab'45'wf_5450 (coe v0) (coe v1) (coe v3) (coe v7) in
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
         C_notFun_1004 v5 -> coe C_failure_100 (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
